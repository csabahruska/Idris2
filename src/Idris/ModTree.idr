module Idris.ModTree

import Core.Binary
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Metadata
import Core.Options
import Core.InitPrimitives
import Core.UnifyState

import Idris.Parser
import Idris.ProcessIdr
import Idris.REPL.Common
import Idris.Syntax
import Idris.Pretty

import Data.Nat
import Data.List
import Data.Either
import Data.String
import Data.SortedMap
import Data.SortedSet
import Data.IORef

import System
import System.Directory
import System.Concurrency

import Libraries.Data.StringMap
import Libraries.Data.String.Extra as Extra

%default covering

record ModTree where
  constructor MkModTree
  nspace : ModuleIdent
  sourceFile : Maybe String
  deps : List ModTree

covering
Show ModTree where
  show t = show (sourceFile t) ++ " " ++ show (nspace t) ++ "<-" ++ show (deps t)

-- A module file to build, and its list of dependencies
-- From this we can work out if the source file needs rebuilding, assuming
-- things are build in dependency order. A source file needs rebuilding
-- if:
--  + Its corresponding ttc is older than the source file
--  + Any of the import ttcs are *newer* than the corresponding ttc
--    (If so: also any imported ttc's fingerprint is different from the one
--    stored in the source file's ttc)
public export
record BuildMod where
  constructor MkBuildMod
  buildFile : String
  buildNS : ModuleIdent
  imports : List ModuleIdent

export
Show BuildMod where
  show t = buildFile t ++ " [" ++ showSep ", " (map show (imports t)) ++ "]"

data AllMods : Type where

mkModTree : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            {auto a : Ref AllMods (List (ModuleIdent, ModTree))} ->
            FC ->
            (done : List ModuleIdent) -> -- if 'mod' is here we have a cycle
            (modFP : Maybe FileName) -> -- Sometimes we know already know what the file name is
            (mod : ModuleIdent) ->      -- Otherwise we'll compute it from the module name
            Core ModTree
mkModTree loc done modFP mod
  = if mod `elem` done
       then throw (CyclicImports (done ++ [mod]))
       else
          -- Read imports from source file. If the source file isn't
          -- available, it's not our responsibility
          catch (do all <- get AllMods
                    -- If we've seen it before, reuse what we found
                    case lookup mod all of
                         Nothing =>
                           do file <- maybe (nsToSource loc mod) pure modFP
                              modInfo <- readHeader file mod
                              let imps = map path (imports modInfo)
                              if mod `elem` imps
                                then coreFail $ CyclicImports [mod, mod]
                                else do
                                  ms <- traverse (mkModTree loc (mod :: done) Nothing) imps
                                  let mt = MkModTree mod (Just file) ms
                                  update AllMods ((mod, mt) ::)
                                  pure mt
                         Just m => pure m)
                -- Couldn't find source, assume it's in a package directory
                (\err =>
                    case err of
                         CyclicImports {} => throw err
                         ParseFail {} => throw err
                         LexFail {} => throw err
                         LitFail {} => throw err
                         _ => pure (MkModTree mod Nothing []))

data DoneMod : Type where
data BuildOrder : Type where

-- Given a module tree, returns the modules in the reverse order they need to
-- be built, including their dependencies
mkBuildMods : {auto d : Ref DoneMod (StringMap ())} ->
              {auto o : Ref BuildOrder (List BuildMod)} ->
              ModTree -> Core ()
mkBuildMods mod
    = whenJust (sourceFile mod) $ \ sf =>
            do done <- get DoneMod
               case lookup sf done of
                    Just _ => pure ()
                    Nothing =>
                       do -- build dependencies
                          traverse_ mkBuildMods (deps mod)
                          -- build it now
                          update BuildOrder
                                   (MkBuildMod sf mod.nspace
                                               (map nspace mod.deps) ::)
                          update DoneMod $ insert sf ()

-- Given a main file name, return the list of modules that need to be
-- built for that main file, in the order they need to be built
-- Return an empty list if it turns out it's in the 'done' list
export
getBuildMods : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               FC -> (done : List BuildMod) ->
               (mainFile : String) ->
               Core (List BuildMod)
getBuildMods loc done fname
    = do a <- newRef AllMods []
         fname_ns <- ctxtPathToNS fname
         if fname_ns `elem` map buildNS done
            then pure []
            else
              do t <- mkModTree {a} loc [] (Just fname) fname_ns
                 dm <- newRef DoneMod empty
                 o <- newRef BuildOrder []
                 mkBuildMods {d=dm} {o} t
                 pure (reverse !(get BuildOrder))

checkTotalReq : {auto c : Ref Ctxt Defs} ->
                String -> String -> TotalReq -> Core Bool
checkTotalReq sourceFile ttcFile expected
  = catch (do log "totality.requirement" 20 $
                "Reading totalReq from " ++ ttcFile
              Just got <- readTotalReq ttcFile
                | Nothing => pure False
              log "totality.requirement" 20 $ unwords
                [ "Got", show got, "and expected", show expected ++ ":"
                , "we", ifThenElse (got < expected) "should" "shouldn't"
                , "rebuild" ]
              -- if what we got (i.e. what we used when we checked the file the
              -- first time around) was strictly less stringent than what we
              -- expect now then we need to rebuild.
              pure (got < expected))
          (\error => pure False)

needsBuildingTime : {auto c : Ref Ctxt Defs} ->
                    (sourceFile : String) -> (ttcFile : String) ->
                    (depFiles : List String) -> Core Bool
needsBuildingTime sourceFile ttcFile depFiles
  = isTTCOutdated ttcFile (sourceFile :: depFiles)

needsBuildingDepHash : {auto c : Ref Ctxt Defs} ->
                 String -> Core Bool
needsBuildingDepHash depFileName
  = catch (do defs                   <- get Ctxt
              depTTCFileName         <- getTTCFileName depFileName "ttc"
              not <$> unchangedHash defs.options.hashFn depTTCFileName depFileName)
          (\error => pure False)

||| Build from source if any of the dependencies, or the associated source file,
||| have been modified from the stored hashes.
needsBuildingHash : {auto c : Ref Ctxt Defs} ->
                    (sourceFile : String) -> (ttcFile : String) ->
                    (depFiles : List String) -> Core Bool
needsBuildingHash sourceFile ttcFile depFiles
  = do defs                <- get Ctxt
       sourceUnchanged <- unchangedHash defs.options.hashFn ttcFile sourceFile
       depFilesHashDiffers <- any id <$> traverse needsBuildingDepHash depFiles
       pure $ (not sourceUnchanged) || depFilesHashDiffers

export
needsBuilding :
  {auto c : Ref Ctxt Defs} ->
  {auto o : Ref ROpts REPLOpts} ->
  (sourceFile, ttcFile : String) -> List String -> Core Bool
needsBuilding sourceFile ttcFile depFiles
  = do -- if the ttc file does not exist there is no point in asking
       -- whether we need to rebuild it
       True <- coreLift $ exists ttcFile
         | False => pure True
       -- check if hash match
       checkHashesInsteadOfTime <- checkHashesInsteadOfModTime <$> getSession
       False <- ifThenElse checkHashesInsteadOfTime
                           needsBuildingHash
                           needsBuildingTime
                  sourceFile ttcFile depFiles
         | True => pure True

       log "import" 20 $ "\{ifThenElse checkHashesInsteadOfTime "Hashes" "Mod Times"} still valid for " ++ sourceFile

       False <- missingIncremental ttcFile
         | True => pure True

       -- in case we're loading the main file, make sure the TTC is
       -- using the appropriate default totality requirement
       Just f <- mainfile <$> get ROpts
         | Nothing => pure False
       log "totality.requirement" 10 $ concat {t = List}
         [ "Checking totality requirement of "
         , sourceFile
         , " (main file is "
         , f
         , ")"
         ]
       let True = sourceFile == f
         | False => pure False
       True <- checkTotalReq sourceFile ttcFile !(totalReq <$> getSession)
         | False => pure False
       -- if it needs rebuilding then remove the buggy .ttc file to avoid going
       -- into an infinite loop!
       Right () <- coreLift $ removeFile ttcFile
         | Left err => throw (FileErr ttcFile err)
       pure True

buildMod : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           FC -> Nat -> Nat -> BuildMod ->
           Core (List Error)
buildMod loc num len mod
   = do clearCtxt; addPrimitives
        lazyActive True; setUnboundImplicits True

        let sourceFile = buildFile mod
        let modNamespace = buildNS mod
        ttcFile <- getTTCFileName sourceFile "ttc"
        -- We'd expect any errors in nsToPath to have been caught by now
        -- since the imports have been built! But we still have to check.
        depFilesE <- traverse (nsToPath loc) (imports mod)
        let (ferrs, depFiles) = partitionEithers depFilesE

        log "import" 20 $ unwords $
          [ "Checking whether to rebuild "
          , sourceFile
          , "(" ++ ttcFile ++ ")"
          , "with dependencies:"
          ] ++ depFiles
        rebuild <- needsBuilding sourceFile ttcFile depFiles

        u <- newRef UST initUState
        m <- newRef MD (initMetadata (PhysicalIdrSrc modNamespace))
        put Syn initSyntax

        errs <- ifThenElse (not rebuild) (pure []) $
           do let pad = minus (length $ show len) (length $ show num)
              let msgPrefix : Doc IdrisAnn
                  = pretty0 (replicate pad ' ') <+> byShow num
                    <+> slash <+> byShow len <+> colon
              let buildMsg : Doc IdrisAnn
                  = pretty0 mod.buildNS
                    <++> parens (pretty0 sourceFile)
              log "import.file" 10 $ "Processing " ++ sourceFile
              process {u} {m} msgPrefix buildMsg sourceFile modNamespace

        ws <- emitWarningsAndErrors (if null errs then ferrs else errs)
        pure (ws ++ if null errs then ferrs else ferrs ++ errs)

export
buildMods : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            FC -> Nat -> Nat -> List BuildMod ->
            Core (List Error)
buildMods fc num len [] = pure []
buildMods fc num len (m :: ms)
    = case !(buildMod fc num len m) of
           [] => buildMods fc (1 + num) len ms
           errs => pure errs

{-
fork : (1 prog : IO ()) -> IO ThreadID
threadWait : (1 threadID : ThreadID) -> IO ()

makeChannel : HasIO io => io (Channel a)
channelGet : HasIO io => (chan : Channel a) -> io a
channelPut : HasIO io => (chan : Channel a) -> (val : a) -> io ()

newRef : (0 x : label) -> t -> Core (Ref x t)
get : (0 x : label) -> {auto ref : Ref x a} -> Core a
put : (0 x : label) -> {auto ref : Ref x a} -> a -> Core ()

coreRun : Core a -> (Error -> IO b) -> (a -> IO b) -> IO b

    coreRun (stMain cgs opts)
      (\err : Error => do ignore $ fPutStrLn stderr $ "Uncaught error: " ++ show err
                          exitWith (ExitFailure 1))
      (\res => pure ())

makeSemaphore : HasIO io => Int -> io Semaphore
semaphorePost : HasIO io => Semaphore -> io ()
semaphoreWait : HasIO io => Semaphore -> io ()
-}
buildModsPar : {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               FC -> Nat -> Nat -> List BuildMod ->
               Core (List Error)
buildModsPar fc num_ len mods = do
  {-
    - clone refs
  -}
  c_val <- get Ctxt
  s_val <- get Syn
  o_val <- get ROpts
  --coreLift $ putStrLn "buildModsPar - 1"
  isCancelledRef <- coreLift $ newIORef False
  resChan <- coreLift $ makeChannel
  --coreLift $ putStrLn "buildModsPar - 2"
  numRef <- coreLift $ newIORef 1
  lock <- coreLift $ makeMutex
  let getNum : IO Nat
      getNum = do
        mutexAcquire lock
        n <- readIORef numRef
        writeIORef numRef (n + 1)
        mutexRelease lock
        pure n

  let worker : Semaphore -> List (ModuleIdent, Semaphore) -> BuildMod -> Core ()
      worker sem depTids mod = do
        --coreLift $ putStrLn "buildModsPar - start - worker \{show num} - \{show mod}"
        for_ depTids $ \(i, tid) => do
          --coreLift $ putStrLn "buildModsPar - worker \{show num} - \{show mod.buildNS} - waiting for \{show i}"
          coreLift $ semaphoreWait tid
          coreLift $ semaphorePost tid
          --coreLift $ putStrLn "buildModsPar - worker \{show num} - waiting for \{show i} END"
        --coreLift $ putStrLn "buildModsPar - worker \{show num} - 1"
        isCancelled <- coreLift $ readIORef isCancelledRef
        --coreLift $ putStrLn "buildModsPar - worker \{show num} - 2"
        r <- if isCancelled
          then do
            let e : List Error
                e = []
            --coreLift $ putStrLn "buildModsPar - worker \{show num} - 3"
            pure e
          else do
            c <- newRef Ctxt c_val
            s <- newRef Syn s_val
            o <- newRef ROpts o_val
            num <- coreLift getNum
            --coreLift $ putStrLn "buildModsPar - worker \{show num} - 4"
            buildMod {c} {s} {o} fc num len mod
        --coreLift $ putStrLn "buildModsPar - worker \{show num} - 5"
        coreLift $ channelPut resChan r
        --coreLift $ putStrLn "buildModsPar - finished - worker \{show num} - \{show mod.buildNS}"
        coreLift $ semaphorePost sem

  let spawnWorker : Semaphore -> List (ModuleIdent, Semaphore) -> BuildMod -> Core ThreadID
      spawnWorker sem depTids mod = coreLift $ fork $ do
        coreRun (worker sem depTids mod)
          (\err : Error => do ignore $ fPutStrLn stderr $ "Uncaught error: " ++ show err
                              exitWith (ExitFailure 1))
          (\res => pure ())

  let go : SortedMap ModuleIdent (ModuleIdent, Semaphore) -> List BuildMod -> Core ()
      go _ [] = pure ()
      go s (m :: ms) = do
        let getTid : ModuleIdent -> Maybe (ModuleIdent, Semaphore)
            getTid i = lookup i s
            {-
            getTid i = case lookup i s of
              Nothing => assert_total $ idris_crash "no tid for \{show i}"
              Just t  => t
            -}
        let depTids = mapMaybe id $ map getTid m.imports
        --coreLift $ putStrLn "buildModsPar - go - \{show num} - 1"
        sem <- coreLift $ makeSemaphore 0
        tid <- spawnWorker sem depTids m
        --coreLift $ putStrLn "buildModsPar - worker \{show num} - tid: "
        go (insert m.buildNS (m.buildNS, sem) s) ms

  --coreLift $ putStrLn "buildModsPar - 1"
  go empty mods
  --coreLift $ putStrLn "buildModsPar - 2"

  -- process results
  let go2 : Nat -> List (List Error) -> List BuildMod -> Core (List Error)
      go2 num errs [] = pure $ concat errs
      go2 num errs (m :: ms) = do
        case !(coreLift $ channelGet resChan) of
           [] => do
            --coreLift $ putStrLn "buildModsPar - result \{show num} - ok"
            go2 (num + 1) errs ms
           e  => do
            --coreLift $ putStrLn "buildModsPar - result \{show num} - error"
            coreLift $ writeIORef isCancelledRef True
            --coreLift $ putStrLn "buildModsPar - go2 - 2"
            go2 (num + 1) (e :: errs) ms

  --coreLift $ putStrLn "buildModsPar - 3"
  go2 1 [] mods
  {-
    - error channel
    - wait for deps to finish
    - had error flag
  -}
  {-
    1) start
        - return 
    2) collect
  -}
  {-
    idea:
      - deps: wait for threads
      - main: wait for each result via channels
  -}

{-
  new design: work stealing
  idea:
    N workers
    one work queue
    one work query function
    task states: todo, work-in-progress, done
    one task finished ack function

    when there is no work then the worker goes to sleep and will wait for a wake up event, which is sent by the task ack function

    data structures:
      mods      : Map ModuleIdent BuildMod
      ready     : SortedMap Int [ModuleIdent] -- prioritise which blocks more
        IDEA for ranking factors:
          + number of blocked modules
          + weight rankings transitively ; i.e. use childrend ranking also with some weights
          Q: use single step ranking function or is the weighted transitive ranking function better?
      blockedBy : Map ModuleIdent [ModuleIdent]
      blockes   : Map ModuleIdent [ModuleIdent]

    init: build ready and blocked from mod list and mods

  TODO:
    done - replace conditionBroadcast with explicit worker thread wakeup management
    CANCEL - use global rank ; transitive closure of deps ; precalculate ranks
    - new rank design ; save and reuse module build times

  TODO:
    RANK DESIGN:
      - critical path method (CPM) ; longest dependency chain -> higher rank
      - shortest job first (SJF)
-}

record Work where
  constructor MkWork
  mods      : SortedMap ModuleIdent BuildMod
  ready     : SortedMap Int (List BuildMod)
  blockedBy : SortedMap ModuleIdent (List ModuleIdent)
  blocks    : SortedMap ModuleIdent (List ModuleIdent)
  critical  : SortedMap ModuleIdent Nat -- critical path length
  errors    : Maybe (Nat, List (List Error))
  num       : Nat
  readySize : Nat -- TODO: wake up workers when necessary
  sleepNum  : Nat

initWork : List BuildMod -> Work
initWork l = initReadySize . initReady . initCriticalPath . initBlocks $ foldl upd w0 l
  where

    getRank : Work -> ModuleIdent -> Int
    getRank w m = case lookup m w.critical of
      Nothing => assert_total $ idris_crash "getRank1"
      Just r  => negate $ cast $ r

    initCriticalPath : Work -> Work
    initCriticalPath w = foldl go w (reverse l) where

      getCritical : Work -> ModuleIdent -> Nat
      getCritical w m = case lookup m w.critical of
        Nothing => assert_total $ idris_crash "getCritical"
        Just n  => 1 + n

      getBlocks : Work -> ModuleIdent -> List ModuleIdent
      getBlocks w m = case lookup m w.blocks of
        Nothing => []
        Just n  => n

      go : Work -> BuildMod -> Work
      go w m = {critical $= insert m.buildNS (concatMap @{Maximum} (getCritical w) (getBlocks w m.buildNS))} w

    initReadySize : Work -> Work
    initReadySize w = {readySize := length $ concat $ values w.ready} w

    initReady : Work -> Work
    initReady w = {ready := fromListWith (++) [(getRank w m.buildNS, [m]) | m <- l, isNothing (lookup m.buildNS w.blockedBy)]} w

    initBlocks : Work -> Work
    initBlocks w = {blocks := fromListWith (++) [(b, [a]) | (a, l) <- kvList w.blockedBy, b <- l]} w

    upd : Work -> BuildMod -> Work
    upd w m =
      case filter (isJust . lookup' w.mods) m.imports of
        []  => w
        il  => {blockedBy $= insert m.buildNS il} w

    w0 = MkWork
      { mods      = fromList [(m.buildNS, m) | m <- l]
      , ready     = empty
      , blockedBy = empty
      , blocks    = empty
      , critical  = empty
      , errors    = Nothing
      , num       = 1
      , readySize = 0
      , sleepNum  = 0
      }

data WorkerCommand
  = Job Nat BuildMod
  | NoWork
  | Finished

exportBuildDeps : String -> List BuildMod -> Core ()
exportBuildDeps fp mods = do
  let s = fromList [m.buildNS | m <- mods]
      fEdges = fp ++ "-edges.tsv"
      fNodes = fp ++ "-nodes.tsv"
  Right () <- coreLift $ writeFile fNodes $ unlines $ "ID\tlabel" :: ["\{show m.buildNS}\t\{show m.buildNS}" | m <- mods]
    | Left err => throw (FileErr fNodes err)
  Right () <- coreLift $ writeFile fEdges $ unlines $ "Source\tTarget" :: ["\{show m.buildNS}\t\{show i}" | m <- mods, i <- m.imports, contains i s]
    | Left err => throw (FileErr fEdges err)
  pure ()

buildModsPar2 : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto o : Ref ROpts REPLOpts} ->
                FC -> Nat -> Nat -> List BuildMod ->
                Core (List Error)
buildModsPar2 fc num_ len mods = do

  --coreLift $ putStrLn "buildModsPar2"
  --coreLift $ for_ mods $ \m => putStrLn "\{show m}"

  for_ mods $ \m => makeBuildDirectory m.buildNS

  --exportBuildDeps "\{!(ttcBuildDirectory)}/build-deps" mods

  let numWorkers = 3

  -- clone refs
  c_val <- get Ctxt
  s_val <- get Syn
  o_val <- get ROpts

  resChan <- coreLift $ makeChannel

  cvMutex <- coreLift $ makeMutex
  cv <- coreLift $ makeCondition

  workMutex <- coreLift $ makeMutex
  let iw0 = initWork mods
  --coreLift $ putStrLn "initWork.ready"
  --coreLift $ for_ iw0.ready $ \m => putStrLn "\{show m}"

  --coreLift $ putStrLn "initWork.critical"
  --coreLift $ for_ (sortBy (\(_,a), (_,b) => compare a b) $ Data.SortedMap.toList iw0.critical) $ \(m, n) => putStrLn "\{show n} - \{show m}"

  workRef <- coreLift $ newIORef iw0

  let mergeErrors : List (List Error) -> Maybe (ModuleIdent, List Error) -> List (List Error)
      mergeErrors errs Nothing = errs
      mergeErrors errs (Just (_, e)) = e :: errs

  let markDone : ModuleIdent -> Work -> Work
      markDone modId work =
        let l = fromMaybe [] $ lookup modId work.blocks
        in foldl upd ({blocks $= delete modId} work) l
       where
        getMod : ModuleIdent -> BuildMod
        getMod mi = case lookup mi work.mods of
          Nothing => assert_total $ idris_crash "markDone4 \{show mi}"
          Just m  => m

        getRank : ModuleIdent -> Int
        getRank mi = case lookup mi work.critical of
          Nothing => assert_total $ idris_crash "getRank \{show mi}"
          Just r  => negate $ cast r -- negate is to make the largest number to be the left most in the sorted map for the pop operation

        upd : Work -> ModuleIdent -> Work
        upd w mi =
          let Just l = lookup mi w.blockedBy
                | Nothing => assert_total $ idris_crash "markDone2 \{show mi}"
          in case [m | m <- l, m /= modId] of
                [] => { ready     $= insertWith (++) (getRank mi) [getMod mi]
                      , readySize $= S
                      , blockedBy $= delete mi } w
                x  => { blockedBy $= insert mi x} w
      {-
          ready     : SortedMap Int (List BuildMod)
          blockedBy : SortedMap ModuleIdent (List ModuleIdent)
          blocks    : SortedMap ModuleIdent (List ModuleIdent)
        update
          - blocks ;
            done + remove key
                 + update blockedBy by removing finished ModuleIdent
          - blockedBy ; if not blocked then remove key and add to ready
          - ready ; lookup rank from blocks map ; HINT: it's ModuleIdent must present in that map
      -}

  let getWork : Nat -> Maybe (ModuleIdent, List Error) -> IO WorkerCommand
      nextJob : Nat -> Work -> IO WorkerCommand

      nextJob i work = do
       --putStrLn "nextJob \{show i} ready: \{show $ [(r, map buildNS m) | (r,m) <- kvList work.ready]}"
       case (pop work.ready, null work.blockedBy) of
        (Nothing, True) => do
          --putStrLn "nextJob \{show i} - DONE"
          writeIORef workRef ({errors := Just (numWorkers, [])} work)
          conditionBroadcast cv
          mutexRelease workMutex
          --putStrLn "nextJob \{show i} - DONE - released"
          getWork i Nothing
        (Nothing, False) => do
          --putStrLn "nextJob \{show i} - SLEEP"
          writeIORef workRef ({sleepNum $= S} work)
          mutexRelease workMutex
          --putStrLn "nextJob \{show i} - SLEEP - released"
          pure NoWork
        (Just ((_, []), ready'), _) => do
          --putStrLn "nextJob \{show i} - AGAIN"
          nextJob i ({ready := ready'} work)
        (Just ((rank, mod :: mods), ready'), _) => do
          --putStrLn "nextJob \{show i} - DO NEXT JOB \{show work.num}"
          let wakeUpWorkers : Nat -> Work -> IO Work
              wakeUpWorkers n w = case (n, w.sleepNum) of
                (S nJob, S nWorker) => do
                  conditionSignal cv
                  wakeUpWorkers nJob ({sleepNum := nWorker} w)
                _ => pure w
          let w1 = {ready := insert rank mods ready', num $= (+) 1, readySize $= pred} work
          w2 <- wakeUpWorkers w1.readySize w1
          writeIORef workRef w2
          -- TODO: wake up sleeping worker threads
          mutexRelease workMutex
          --putStrLn "nextJob \{show i} - DO NEXT JOB \{show work.num} - released"
          pure $ Job work.num mod

      getWork i result = do
        --putStrLn "getWork \{show i} \{show result}"
        mutexAcquire workMutex
        --putStrLn "getWork \{show i} \{show result} - locked"
        --whenJust result $ \_ => do
          --conditionBroadcast cv
          --putStrLn "getWork \{show i} \{show result} - broadcast"
        work <- readIORef workRef
        Nothing <- pure work.errors
          -- exit
          | Just (0, errs) => assert_total $ idris_crash "getWork"
          | Just (1, errs) => do
            --putStrLn "getWork \{show i} EXIT"
            channelPut resChan $ concat $ mergeErrors errs result
            --putStrLn "getWork \{show i} EXIT - final result sent"
            mutexRelease workMutex
            --putStrLn "getWork \{show i} EXIT - released"
            pure Finished
          -- wait for worker threads
          | Just (S n, errs) => do
            --putStrLn "getWork \{show i} WAIT FOR WORKERS TO FINISH \{show n}"
            writeIORef workRef ({errors := Just (n, mergeErrors errs result)} work)
            mutexRelease workMutex
            --putStrLn "getWork \{show i} WAIT FOR WORKERS TO FINISH \{show n} - released"
            pure Finished
        case result of
          Nothing => nextJob i work
          Just (modId, []) => nextJob i $ markDone modId work
          Just (_, errs) => do
            --putStrLn "getWork \{show i} ERROR"
            writeIORef workRef ({errors := Just (numWorkers, [])} work)
            conditionBroadcast cv
            mutexRelease workMutex
            --putStrLn "getWork \{show i} ERROR - released"
            getWork i result

        {-
          TODO:
            - process result
              + ok: update blocking structures and ready queue
              + error: collect results and wait for all workers to finish by waiting for (N-1) getWork in-calls
        -}

  let worker : Nat -> WorkerCommand -> Core ()
      worker i Finished = do
        --coreLift $ putStrLn "worker \{show i} - Finished"
        pure ()
      worker i NoWork = do
        coreLift $ do
          --putStrLn "worker \{show i} - NoWork"
          mutexAcquire cvMutex
          --putStrLn "worker \{show i} - NoWork - sleep - start"
          conditionWait cv cvMutex
          --putStrLn "worker \{show i} - NoWork - sleep - ended"
          mutexRelease cvMutex
        coreLift (getWork i Nothing) >>= worker i
      worker i (Job num mod) = do
        --coreLift $ putStrLn "START worker \{show i} - Job \{show num} \{show mod}"
        c <- newRef Ctxt c_val
        s <- newRef Syn s_val
        o <- newRef ROpts o_val
        r <- {-logTimeWhen {c} True 0 "\{show num}/\{show len} \{show mod.buildNS}" $ -}buildMod {c} {s} {o} fc num len mod
        --coreLift $ putStrLn "FINISHED worker \{show i} - done - Job \{show num} \{show mod}"
        coreLift (getWork i (Just (mod.buildNS, r))) >>= worker i

  let spawnWorker : Nat -> Core ThreadID
      spawnWorker i = coreLift $ fork $ do
        coreRun (coreLift (getWork i Nothing) >>= worker i)
          (\err : Error => do ignore $ fPutStrLn stderr $ "Uncaught error: " ++ show err
                              exitWith (ExitFailure 1))
          (\res => pure ())

  worker_tids <- for [1..numWorkers] spawnWorker

  -- wait for results
  coreLift $ channelGet resChan

export
buildDeps : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto o : Ref ROpts REPLOpts} ->
            (mainFile : String) ->
            Core (List Error)
buildDeps fname
    = do mods <- getBuildMods EmptyFC [] fname
         log "import" 20 $ "Needs to rebuild: " ++ show mods
         ok <- buildModsPar2 EmptyFC 1 (length mods) mods
         case ok of
              [] => do -- On success, reload the main ttc in a clean context
                       clearCtxt; addPrimitives
                       modIdent <- ctxtPathToNS fname
                       put MD (initMetadata (PhysicalIdrSrc modIdent))
                       mainttc <- getTTCFileName fname "ttc"
                       log "import" 10 $ "Reloading " ++ show mainttc ++ " from " ++ fname
                       readAsMain mainttc

                       -- Load the associated metadata for interactive editing
                       mainttm <- getTTCFileName fname "ttm"
                       log "import" 10 $ "Reloading " ++ show mainttm
                       readFromTTM mainttm
                       pure []
              errs => pure errs -- Error happened, give up

getAllBuildMods : {auto c : Ref Ctxt Defs} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  FC -> (done : List BuildMod) ->
                  (allFiles : List String) ->
                  Core (List BuildMod)
getAllBuildMods fc done [] = pure done
getAllBuildMods fc done (f :: fs)
    = do ms <- getBuildMods fc done f
         getAllBuildMods fc (ms ++ done) fs

export
buildAll : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           (allFiles : List String) ->
           Core (List Error)
buildAll allFiles
    = do mods <- getAllBuildMods EmptyFC [] allFiles
         -- There'll be duplicates, so if something is already built, drop it
         let mods' = dropLater mods
         buildModsPar2 EmptyFC 1 (length mods') mods'
  where
    dropLater : List BuildMod -> List BuildMod
    dropLater [] = []
    dropLater (b :: bs)
        = b :: dropLater (filter (\x => buildFile x /= buildFile b) bs)
