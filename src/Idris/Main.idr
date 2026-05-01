module Idris.Main

import Idris.Driver
import Compiler.Common

import Core.Env
import Core.Value
import Core.Context
import Idris.Syntax
import Libraries.Utils.Path

compile :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (outputDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile defs1 syn tmp outputDir term outfile = do
  let out = outputDir </> outfile

  defs <- get Ctxt
  t <- nf defs [] term
  q <- quote defs [] t
  t <- toFullNames q
  let res = "\{show t}"
  coreLift $ putStrLn "execute:\n\{show t}"
  Core.writeFile out "compile:\n\{res}"
  pure (Just out)

{-
      defs <- get Ctxt
      logC "staging" 20 $ pure "PApp - tmx: \{show !(toFullNames !(quote defs env tmx))}"
      logC "staging" 20 $ pure "PApp - tmy: \{show !(toFullNames !(quote defs env tmy))}"

      computation <- getRef vars emptyFC $ NS (MkNS ["Staging"]) $ UN $ Basic "Computation"
      _ <- unify mode loc env !(quote defs env p) computation

nf : {auto c : Ref Ctxt Defs} ->
     {vars : _} ->
     Defs -> Env Term vars -> Term vars -> Core (NF vars)
-}

{-
compileExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) ->
  (outputDir : String) ->
  ClosedTerm ->
  (outfile : String) ->
  Core (Maybe String)
compileExpr c s tmpDir outputDir tm outfile =
  do es <- compileToJS c s tm
     let res = addHeaderAndFooter outfile es
     let out = outputDir </> outfile
     Core.writeFile out res
     pure (Just out)
-}

execute :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (execDir : String) -> ClosedTerm -> Core ()
execute defs1 syn dir term = do
  defs <- get Ctxt
  t <- nf defs [] term
  q <- quote defs [] t
  t <- toFullNames q
  coreLift $ putStrLn "\{show t}"

stagingCodegen : Codegen
stagingCodegen = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("staging", stagingCodegen)]
