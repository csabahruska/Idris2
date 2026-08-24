# haskell_stage

// builtins
Ty   : Type
Code : Ty -> Type
Arr  : Ty -> Ty -> Ty
Lam  : {a b} -> (Code a -> Code b) -> Code (Arr a b)
App  : {a b} -> Code (Arr a b) -> Code a -> Code b
Let  : {a b} -> Code a -> (Code a -> Code b) -> Code b

Prod : Ty -> Ty -> Ty
Pair : {a b} -> Code a -> Code b -> Code (Prod a b)
Fst  : {a b} -> Code (Prod a b) -> Code a
Snd  : {a b} -> Code (Prod a b) -> Code b

Unit :: Type
TT   :: Unit

// builtins
Cons : String -> String -> String
ProdStr : Type
PairStr : String -> String -> ProdStr
AppendStr : ProdStr -> String
EqStr     : ProdStr -> Nat

appendStr : String -> String -> String
  = \a b -> AppendStr (PairStr a b)

Succ : Nat -> Nat

// FFI


/*
  USE CASES:
    - process input string compile time and interpret/evaluate it to a number ; may need compile time I/O
    - process input string compile time (compiler)
    - process input string run time     (interpreter)
*/

/*
input lang
x = 1
b = x
y = x + 2
z = x * b
w = 1 * 0
*/

/*
  optimizations:
    done - copy propagation
    - multiply by 1 or 0
*/

/*
  add user input command : get x
*/

// Backend primitives
OString :: Type
MkOString : String -> Code OString

ONat :: Type
MkONat : Nat -> Code ONat

AddOp   :: ONat -> ONat -> ONat
MulOp   :: ONat -> ONat -> ONat

Dbg :: OString -> ONat -> ONat

Dec : {a b} -> (Code a -> Code b) -> Code b
Def : {a b} -> Code a -> Code a -> Code b -> Code b


//   Fix f = Dec \g -> Def g (f g) g
//f_Fix : {a} -> (Code a -> Code a) -> Code a
//f_Fix fn = (f := fn ; Dec \g -> (fg := f g ; Def g fg g))

MatchSuc : {a} -> Code ONat -> Code a -> (Code ONat -> Code a) -> Code a

example : Code ONat
example =
  Dec \even ->
    Dec \odd ->
      Def even (\n -> MatchSuc n (MkONat 1) (\n -> odd n))
        (Def odd  (\n -> MatchSuc n (MkONat 0) (\n -> even n))
          (even (MkONat 12)))



// ---------------------
// AST obj

/*
input lang
x = 1
b = x
y = x + 2
z = x * b
w = 1 * 0

data OArg
  = ONum ONat
  | OVar OString

OVal : Code OString -> Code OArg -> Code OExp
*/

OArg :: Type
ONum :: ONat -> OArg
OVar :: OString -> OArg

OExp :: Type
OVal :: OString -> OArg -> OExp
OAdd :: OString -> OArg -> OArg -> OExp
OMul :: OString -> OArg -> OArg -> OExp


// AST meta

Arg : Type
Num : Nat -> Arg
Var : String -> Arg

Exp : Type
Val : String -> Arg -> Exp
Add : String -> Arg -> Arg -> Exp
Mul : String -> Arg -> Arg -> Exp

// List

List      : Type -> Type
ListCons  : {a} -> a -> List a -> List a
ListNil   : {a} -> List a

OList      : Ty -> Ty
OListCons  : {a} -> Code a -> Code (OList a) -> Code (OList a)
OListNil   : {a} -> Code (OList a)


map : {a b} -> (a -> b) -> List a -> List b
map f ListNil = ListNil
map f (ListCons e es) = ListCons (f e) (map f es)

test_listMeta = ListCons "hello" (ListCons "world" ListNil)
test_listObj  = ListCons (MkOString "hello") (ListCons (MkOString "world") ListNil)

words_collect : String -> String -> List String
words_skip : String -> List String
words : String -> List String

words s = words_skip s

words_skip "" = ListNil
words_skip (Cons " " cs) = words_skip cs
words_skip (Cons c cs) = words_collect c cs

words_collect w "" = ListCons w ListNil
words_collect w (Cons " " cs) = ListCons w (words_skip cs)
words_collect w (Cons c cs) = words_collect (appendStr w c) cs

Bool : Type
True  : Bool
False : Bool

and : Bool -> Bool -> Bool
and True True = True
and a b       = False

or : Bool -> Bool -> Bool
or False False = False
or a b         = True

natToBool : Nat -> Bool
natToBool 1 = True
natToBool _ = False

eqStr : String -> String -> Bool
  = \a b -> natToBool (EqStr (PairStr a b))

isNumberChar : String -> Bool
isNumberChar "0" = True
isNumberChar "1" = True
isNumberChar "2" = True
isNumberChar "3" = True
isNumberChar "4" = True
isNumberChar "5" = True
isNumberChar "6" = True
isNumberChar "7" = True
isNumberChar "8" = True
isNumberChar "9" = True
isNumberChar  c  = False

// compiled version
OBool :: Type
OTrue  :: OBool
OFalse :: OBool

// string  comparison
OEqStr : Code OString -> Code OString -> Code OBool

// constructor testing and arg projection
OIsCon : {a} -> String -> Code a -> Code OBool
OConProj : {a} -> {b} -> Nat -> Code a -> Code b

Oite : {a} -> Code OBool -> Code a -> Code a -> Code a

compiled_isNumberChar : Code OString -> Code OBool
//compiled_isNumberChar : Code (OString -> OBool)
compiled_isNumberChar := \s ->
  Oite (OEqStr s (MkOString "0")) OTrue (
  Oite (OEqStr s (MkOString "1")) OTrue (
  Oite (OEqStr s (MkOString "2")) OTrue (
  Oite (OEqStr s (MkOString "3")) OTrue (
  Oite (OEqStr s (MkOString "4")) OTrue (
  Oite (OEqStr s (MkOString "5")) OTrue (
  Oite (OEqStr s (MkOString "6")) OTrue (
  Oite (OEqStr s (MkOString "7")) OTrue (
  Oite (OEqStr s (MkOString "8")) OTrue (
  Oite (OEqStr s (MkOString "9")) OTrue OFalse
  )))))))))

compiled_and : Code OBool -> Code OBool -> Code OBool
compiled_and := \ a b ->
  Oite (OIsCon "OTrue" a)
    (Oite (OIsCon "OTrue" b) OTrue OFalse)
    OFalse

OCons_head : Code OString -> Code OString
OCons_tail : Code OString -> Code OString
OAppendStr : Code OString -> Code OString -> Code OString

// obj lang primitive to support recursion
Fix : {a} -> (Code a -> Code a) -> Code a
/*
compiled_allCharIsF : (Code (OString -> OBool) -> Code OString -> Code OBool) -> Code (OString -> OBool) -> Code OString -> Code OBool
compiled_allCharIsF  := \rec f s ->
  Oite (OEqStr s (MkOString "")) OTrue
  ( h := OCons_head s
  ; t := OCons_tail s
  ; compiled_and (f h) (rec f t)
  )

compiled_allCharIs : Code (OString -> OBool) -> Code OString -> Code OBool
compiled_allCharIs := f_Fix compiled_allCharIsF
*/
compiled_allCharIs : Code (OString -> OBool) -> Code OString -> Code OBool
compiled_allCharIs := Dec \compiled_allCharIs -> Def compiled_allCharIs (\f s ->
  Oite (OEqStr s (MkOString "")) OTrue
  ( h := OCons_head s
  ; t := OCons_tail s
  ; compiled_and (f h) (compiled_allCharIs f t)
  )) compiled_allCharIs


compiled_isNumber : Code OString -> Code OBool
compiled_isNumber := compiled_allCharIs compiled_isNumberChar

compiled_reverseString : Code OString -> Code OString
compiled_reverseString := Dec \compiled_reverseString -> Def compiled_reverseString (\s ->
  Oite (OEqStr s (MkOString "")) (MkOString "")
  ( h := OCons_head s
  ; t := OCons_tail s
  ; OAppendStr (compiled_reverseString t) h
  )) compiled_reverseString

OError : {a} -> Code a

compiled_words : Code OString -> Code (OList OString)
compiled_words := \str ->
  Dec \compiled_words_skip ->
    Dec \compiled_words_collect ->
      Def compiled_words_skip
        (\s ->
          Oite (OEqStr s (MkOString "")) OListNil
            ( h := OCons_head s
            ; t := OCons_tail s
            ; Oite (OEqStr h (MkOString " "))
                (compiled_words_skip t)
                (compiled_words_collect h t)
            )
        )
        (Def compiled_words_collect
          (\w s ->
            Oite (OEqStr s (MkOString "")) (OListCons w OListNil)
              ( h := OCons_head s
              ; t := OCons_tail s
              ; Oite (OEqStr h (MkOString " "))
                  (OListCons w (compiled_words_skip t))
                  (compiled_words_collect (OAppendStr w h) t)
              )
          )
          (compiled_words_skip str)
        )

compiled_parseDigit : Code OString -> Code ONat
compiled_parseDigit := \s ->
  Oite (OEqStr s (MkOString "0")) (MkONat 0) (
  Oite (OEqStr s (MkOString "1")) (MkONat 1) (
  Oite (OEqStr s (MkOString "2")) (MkONat 2) (
  Oite (OEqStr s (MkOString "3")) (MkONat 3) (
  Oite (OEqStr s (MkOString "4")) (MkONat 4) (
  Oite (OEqStr s (MkOString "5")) (MkONat 5) (
  Oite (OEqStr s (MkOString "6")) (MkONat 6) (
  Oite (OEqStr s (MkOString "7")) (MkONat 7) (
  Oite (OEqStr s (MkOString "8")) (MkONat 8) (
  Oite (OEqStr s (MkOString "9")) (MkONat 9) OError
  )))))))))

compiled_parseNat_go : Code OString -> Code ONat -> Code ONat
compiled_parseNat_go := Dec \compiled_parseNat_go -> Def compiled_parseNat_go (\s n ->
  Oite (OEqStr s (MkOString "")) (MkONat 0)
  ( h := OCons_head s
  ; t := OCons_tail s
  ; AddOp (MulOp n (compiled_parseDigit h)) (compiled_parseNat_go h (MulOp n (MkONat 10)))
  )) compiled_parseNat_go

//compiled_parseNat_go : Code OString -> Code ONat -> Code ONat
//compiled_parseNat_go := f_Fix compiled_parseNat_goF

compiled_parseNat : Code OString -> Code ONat
compiled_parseNat := \s -> compiled_parseNat_go (compiled_reverseString s) (MkONat 1)

compiled_parseArg : Code OString -> Code OBool -> Code OArg
compiled_parseArg := \arg b ->
  Oite (OIsCon "OTrue" b)
    (ONum (compiled_parseNat arg))
    (OVar arg)

compiled_parse_match1 : (Code (OList OString) -> Code (OList OExp)) -> Code (OList OString) -> Code (OList OExp)
compiled_parse_match2 : (Code (OList OString) -> Code (OList OExp)) -> Code (OList OString) -> Code (OList OExp)
compiled_parse_match3 : (Code (OList OString) -> Code (OList OExp)) -> Code (OList OString) -> Code (OList OExp)
compiled_parse_match4 : (Code (OList OString) -> Code (OList OExp)) -> Code (OList OString) -> Code (OList OExp)

compiled_parse_match4 := \rec l -> OListNil

compiled_parse_match3 := \rec l0 ->
  Oite (OIsCon "OListCons" l0)
    ( name := OConProj 0 l0
    ; l1 := OConProj 1 l0
    ; Oite (OIsCon "OListCons" l1)
        ( v1 := OConProj 0 l1
        ; l2 := OConProj 1 l1
        ; Oite (OEqStr (MkOString "=") v1)
            ( Oite (OIsCon "OListCons" l2)
                ( arg1 := OConProj 0 l2
                ; l3 := OConProj 1 l2
                ; Oite (OIsCon "OListCons" l3)
                    ( v3 := OConProj 0 l3
                    ; l4  := OConProj 1 l3
                    ; Oite (OEqStr (MkOString "*") v3)
                        ( Oite (OIsCon "OListCons" l4)
                            ( arg2 := OConProj 0 l4
                            ; l5 := OConProj 1 l4
                            ; Oite (OIsCon "OListCons" l5)
                                ( v5 := OConProj 0 l5
                                ; s  := OConProj 1 l5
                                ; Oite (OEqStr (MkOString ";") v5)
                                    (OListCons (OMul name (compiled_parseArg arg1 (compiled_isNumber arg1)) (compiled_parseArg arg2 (compiled_isNumber arg2))) (rec s))
                                    (compiled_parse_match4 rec l0)
                                )
                                (compiled_parse_match4 rec l0)
                            )
                            (compiled_parse_match4 rec l0)
                        )
                        (compiled_parse_match4 rec l0)
                    )
                    (compiled_parse_match4 rec l0)
                )
                (compiled_parse_match4 rec l0)
            )
            (compiled_parse_match4 rec l0)
        )
        (compiled_parse_match4 rec l0)
    )
    (compiled_parse_match4 rec l0)

compiled_parse_match2 := \rec l0 ->
  Oite (OIsCon "OListCons" l0)
    ( name := OConProj 0 l0
    ; l1 := OConProj 1 l0
    ; Oite (OIsCon "OListCons" l1)
        ( v1 := OConProj 0 l1
        ; l2 := OConProj 1 l1
        ; Oite (OEqStr (MkOString "=") v1)
            ( Oite (OIsCon "OListCons" l2)
                ( arg1 := OConProj 0 l2
                ; l3 := OConProj 1 l2
                ; Oite (OIsCon "OListCons" l3)
                    ( v3 := OConProj 0 l3
                    ; l4  := OConProj 1 l3
                    ; Oite (OEqStr (MkOString "+") v3)
                        ( Oite (OIsCon "OListCons" l4)
                            ( arg2 := OConProj 0 l4
                            ; l5 := OConProj 1 l4
                            ; Oite (OIsCon "OListCons" l5)
                                ( v5 := OConProj 0 l5
                                ; s  := OConProj 1 l5
                                ; Oite (OEqStr (MkOString ";") v5)
                                    (OListCons (OAdd name (compiled_parseArg arg1 (compiled_isNumber arg1)) (compiled_parseArg arg2 (compiled_isNumber arg2))) (rec s))
                                    (compiled_parse_match3 rec l0)
                                )
                                (compiled_parse_match3 rec l0)
                            )
                            (compiled_parse_match3 rec l0)
                        )
                        (compiled_parse_match3 rec l0)
                    )
                    (compiled_parse_match3 rec l0)
                )
                (compiled_parse_match3 rec l0)
            )
            (compiled_parse_match3 rec l0)
        )
        (compiled_parse_match3 rec l0)
    )
    (compiled_parse_match3 rec l0)

compiled_parse_match1 := \rec l0 ->
  Oite (OIsCon "OListCons" l0)
    ( name := OConProj 0 l0
    ; l1 := OConProj 1 l0
    ; Oite (OIsCon "OListCons" l1)
        ( v1 := OConProj 0 l1
        ; l2 := OConProj 1 l1
        ; Oite (OEqStr (MkOString "=") v1)
            ( Oite (OIsCon "OListCons" l2)
                ( arg := OConProj 0 l2
                ; l3 := OConProj 1 l2
                ; Oite (OIsCon "OListCons" l3)
                    ( v3 := OConProj 0 l3
                    ; s  := OConProj 1 l3
                    ; Oite (OEqStr (MkOString ";") v3)
                        (OListCons (OVal name (compiled_parseArg arg (compiled_isNumber arg))) (rec s))
                        (compiled_parse_match2 rec l0)
                    )
                    (compiled_parse_match2 rec l0)
                )
                (compiled_parse_match2 rec l0)
            )
            (compiled_parse_match2 rec l0)
        )
        (compiled_parse_match2 rec l0)
    )
    (compiled_parse_match2 rec l0)


compiled_parse : Code (OList OString) -> Code (OList OExp)
compiled_parse := Dec \compiled_parse -> Def compiled_parse (compiled_parse_match1 compiled_parse) compiled_parse

/*
TODO: try to use meta level functions to express pattern matching

parse : List String -> List Exp
// parse (name::"="::arg::";"::s) = (Val name (parseArg arg (isNumber arg))) : (parse s)
parse (ListCons name
      (ListCons "="
      (ListCons arg
      (ListCons ";"
      s
      )))) = ListCons (Val name (parseArg arg (isNumber arg))) (parse s)
parse (ListCons name
      (ListCons "="
      (ListCons arg1
      (ListCons "+"
      (ListCons arg2
      (ListCons ";"
      s
      )))))) = ListCons (Add name (parseArg arg1 (isNumber arg1)) (parseArg arg2 (isNumber arg2))) (parse s)
parse (ListCons name
      (ListCons "="
      (ListCons arg1
      (ListCons "*"
      (ListCons arg2
      (ListCons ";"
      s
      )))))) = ListCons (Mul name (parseArg arg1 (isNumber arg1)) (parseArg arg2 (isNumber arg2))) (parse s)
parse x = ListNil
*/

OEnv : Ty -> Ty
OEmptyEnv : {a} -> Code (OEnv a)
OEntryEnv : {a} -> Code OString -> Code a -> Code (OEnv a) -> Code (OEnv a)

compiled_envLookup : {a} -> Code (OEnv a) -> Code OString -> Code a
// BUG compiled_envLookup := \{a} rec env name ->
compiled_envLookup := \env0 name0 -> Dec \compiled_envLookup -> Def compiled_envLookup (\env name ->
  Oite (OIsCon "OEmptyEnv" env) OError
  (Oite (OIsCon "OEntryEnv" env)
    ( n := OConProj 1 env
    ; v := OConProj 2 env
    ; e := OConProj 3 env
    ; arg1 := OEqStr n name
    ; arg2 := compiled_envLookup e name
    ; Oite arg1 v arg2
    )
    OError
  )) (compiled_envLookup env0 name0)
/*
compiled_envLookup : {a} -> Code (OEnv a) -> Code OString -> Code a
compiled_envLookup := f_Fix compiled_envLookupF
*/
compiled_envInsert : {a} -> Code (OEnv a) -> Code OString -> Code a -> Code (OEnv a)
compiled_envInsert := \e name value -> OEntryEnv name value e

compiled_evalArg : Code OArg -> Code (OEnv ONat) -> Code ONat
compiled_evalArg := \arg env ->
  Oite (OIsCon "OVar" arg)
    ( name := OConProj 0 arg
    ; res := compiled_envLookup env name
    ; res
    )
    (Oite (OIsCon "ONum" arg)
      ( n := OConProj 0 arg
      ; n
      )
      OError
    )

compiled_evalExp_OVal : Code OExp -> Code (OEnv ONat) -> Code (OEnv ONat)
compiled_evalExp_OVal := \exp env ->
  ( name := OConProj 0 exp
  ; arg  := OConProj 1 exp
  ; compiled_envInsert env name (compiled_evalArg arg env)
  )
compiled_evalExp_OAdd : Code OExp -> Code (OEnv ONat) -> Code (OEnv ONat)
compiled_evalExp_OAdd := \exp env ->
  ( name := OConProj 0 exp
  ; arg1 := OConProj 1 exp
  ; arg2 := OConProj 2 exp
  ; compiled_envInsert env name (AddOp (compiled_evalArg arg1 env) (compiled_evalArg arg2 env))
  )
compiled_evalExp_OMul : Code OExp -> Code (OEnv ONat) -> Code (OEnv ONat)
compiled_evalExp_OMul := \exp env ->
  ( name := OConProj 0 exp
  ; arg1 := OConProj 1 exp
  ; arg2 := OConProj 2 exp
  ; compiled_envInsert env name (MulOp (compiled_evalArg arg1 env) (compiled_evalArg arg2 env))
  )
compiled_evalExp : Code OExp -> Code (OEnv ONat) -> Code (OEnv ONat)
compiled_evalExp := \exp env ->
   Oite (OIsCon "OVal" exp) (compiled_evalExp_OVal exp env)
  (Oite (OIsCon "OAdd" exp) (compiled_evalExp_OAdd exp env)
  (Oite (OIsCon "OMul" exp) (compiled_evalExp_OMul exp env)
   OError
  ))

compiled_evalF : (Code (OList OExp) -> Code (OEnv ONat) -> Code (OEnv ONat)) -> Code (OList OExp) -> Code (OEnv ONat) -> Code (OEnv ONat)
compiled_eval : Code (OList OExp) -> Code (OEnv ONat) -> Code (OEnv ONat)
compiled_eval_OListNil : Code (OList OExp) -> Code (OEnv ONat) -> Code (OEnv ONat)
compiled_eval_OListConsF : (Code (OList OExp) -> Code (OEnv ONat) -> Code (OEnv ONat)) -> Code (OList OExp) -> Code (OEnv ONat) -> Code (OEnv ONat)

compiled_eval_OListNil l env = env
compiled_eval_OListConsF := \rec list env ->
  ( exp := OConProj 0 list
  ; l   := OConProj 1 list
  ; rec l (compiled_evalExp exp env)
  )
compiled_eval := Dec \compiled_eval -> Def compiled_eval (\l env ->
   Oite (OIsCon "OListNil" l) (compiled_eval_OListNil l env)
  (Oite (OIsCon "ListCons" l) (compiled_eval_OListConsF compiled_eval l env)
   OError
  )) compiled_eval

//compiled_eval := f_Fix compiled_evalF

// ----------------------

allCharIs : (String -> Bool) -> String -> Bool
allCharIs f "" = True
allCharIs f (Cons c s) = and (f c) (allCharIs f s)

isNumber : String -> Bool
isNumber s = allCharIs isNumberChar s

toCharList : String -> List String
toCharList "" = ListNil
toCharList (Cons a b) = ListCons a (toCharList b)

reverseString : String -> String
reverseString "" = ""
reverseString (Cons c s) = appendStr (reverseString s) c

parseDigit : String -> Nat
parseDigit "0" = 0
parseDigit "1" = 1
parseDigit "2" = 2
parseDigit "3" = 3
parseDigit "4" = 4
parseDigit "5" = 5
parseDigit "6" = 6
parseDigit "7" = 7
parseDigit "8" = 8
parseDigit "9" = 9

natPlus : Nat -> Nat -> Nat
natPlus 0 n = n
natPlus n 0 = n
natPlus n (Succ m) = Succ (natPlus n m)

natMul : Nat -> Nat -> Nat
natMul n 0 = 0
natMul 0 m = 0
natMul (Succ n) m = natPlus m (natMul n m)

parseNat_go : String -> Nat -> Nat
parseNat_go "" n = 0
parseNat_go (Cons c s) n = natPlus (natMul n (parseDigit c)) (parseNat_go s (natMul n 10))

parseNat : String -> Nat
parseNat s = parseNat_go (reverseString s) 1
/*
parseOArg : String -> Bool -> Code OArg
parseOArg arg True   = ONum (MkONat (parseNat arg))
parseOArg arg False  = OVar (MkOString arg)

parseO : List String -> List (Code OExp)
parseO (ListCons name
      (ListCons "="
      (ListCons arg
      (ListCons ";"
      s
      )))) = ListCons (OVal (MkOString name) (parseOArg arg (isNumber arg))) (parseO s)
parseO (ListCons name
      (ListCons "="
      (ListCons arg1
      (ListCons "+"
      (ListCons arg2
      (ListCons ";"
      s
      )))))) = ListCons (OAdd (MkOString name) (parseOArg arg1 (isNumber arg1)) (parseOArg arg2 (isNumber arg2))) (parseO s)
parseO (ListCons name
      (ListCons "="
      (ListCons arg1
      (ListCons "*"
      (ListCons arg2
      (ListCons ";"
      s
      )))))) = ListCons (OMul (MkOString name) (parseOArg arg1 (isNumber arg1)) (parseOArg arg2 (isNumber arg2))) (parseO s)
parseO x = ListNil
*/
parseArg : String -> Bool -> Arg
parseArg arg True   = Num (parseNat arg)
parseArg arg False  = Var arg

parse : List String -> List Exp
parse (ListCons name
      (ListCons "="
      (ListCons arg
      (ListCons ";"
      s
      )))) = ListCons (Val name (parseArg arg (isNumber arg))) (parse s)
parse (ListCons name
      (ListCons "="
      (ListCons arg1
      (ListCons "+"
      (ListCons arg2
      (ListCons ";"
      s
      )))))) = ListCons (Add name (parseArg arg1 (isNumber arg1)) (parseArg arg2 (isNumber arg2))) (parse s)
parse (ListCons name
      (ListCons "="
      (ListCons arg1
      (ListCons "*"
      (ListCons arg2
      (ListCons ";"
      s
      )))))) = ListCons (Mul name (parseArg arg1 (isNumber arg1)) (parseArg arg2 (isNumber arg2))) (parse s)
parse x = ListNil

ite : {a} -> Bool -> a -> a -> a
ite True t e = t
ite False t e = e

Env : Type -> Type
EmptyEnv : {a} -> Env a
EntryEnv : {a} -> String -> a -> Env a -> Env a

envLookup : {a} -> Env a -> String -> a
envLookup (EntryEnv n v e) name = ite (eqStr n name) v (envLookup e name)

envInsert : {a} -> Env a -> String -> a -> Env a
envInsert e name value = EntryEnv name value e

// ---------- runtime time interpretation ---------------------------
/*
  USE CASES:
    - runtime interpreter in C (manual memory management)
    - runtime interpreter in Python (GC)
  required runtime primops:
    done - string cons
    done - string append
    done - string eq
    done - int add
    done - int mul
    done - adt representation for Env, Exp and Arg
    done - pattern match on ADTs
    done - pattern match on String
    done - pattern match on List
  compile to object lang:
    done - envLookup
    done - envInsert
    done - evalArg
    done - evalExp
    done - eval
    done - words_collect ; needs Fix2 or Dec/Def
    done - words_skip    ; needs Fix2 or Dec/Def
    done - words         ; needs Fix2 or Dec/Def
    done - parse
    done - parseArg
    done - parseNat
    done - parseNat_go
    done - parseDigit
    done - isNumber
    done - isNumberChar
    done - allCharIs
    done - reverseString
  runtime prim types:
    done - String
    done - Nat
  runtime ADTs:
    done - Bool
    done - List
    done - Exp
    done - Arg
    done - Env

  NOTE: ideally the compile time interpreter code is the same as the runtime interpreter code, only their types are different

  Q: how to represent ADTs in obj language?
     how to compile ADTs to C or Python?
     can we map some ADTs to object lang's prim types? (python's bool, python's list)

  TODO:
    - write obj compiled version of all functions manually one by one

  IDEA:
    - stage programmable runtime interpreter
      + optional step by step debugger on the terminal
*/

// ---------- compile time interpretation ---------------------------

evalArg : Arg -> Env Nat -> Nat
evalArg (Var name) env = envLookup env name
evalArg (Num n) env = n

evalExp : Exp -> Env Nat -> Env Nat
evalExp (Val name arg) env = envInsert env name (evalArg arg env)
evalExp (Add name arg1 arg2) env = envInsert env name (natPlus (evalArg arg1 env) (evalArg arg2 env))
evalExp (Mul name arg1 arg2) env = envInsert env name (natMul (evalArg arg1 env) (evalArg arg2 env))

eval : List Exp -> Env Nat -> Env Nat
eval ListNil env = env
eval (ListCons exp l) env = eval l (evalExp exp env)

// ------------ test

// ---------- compilation with data deps only ---------------------------

compArg' : Arg -> Env (Code ONat) -> Code ONat
compArg' (Var name) env = envLookup env name
compArg' (Num n) env = MkONat n

compExp' : Exp -> Env (Code ONat) -> Env (Code ONat)
compExp' (Val name arg) env = envInsert env name (r := Dbg (MkOString name) (compArg' arg env) ; r)
compExp' (Add name arg1 arg2) env = envInsert env name (r := Dbg (MkOString name) (AddOp (compArg' arg1 env) (compArg' arg2 env)) ; r)
compExp' (Mul name arg1 arg2) env = envInsert env name (r := Dbg (MkOString name) (MulOp (compArg' arg1 env) (compArg' arg2 env)) ; r)

compile' : List Exp -> Env (Code ONat) -> Env (Code ONat)
compile' ListNil env = env
compile' (ListCons exp l) env = compile' l (compExp' exp env)

// -----------------
/*
Q: how to unify the interpreter and the compiler code?
Q: how to turn the compile time interpreter to runtime interpreter?
*/
// ------- compilation with continuations ------------------------------------------

compArg : Arg -> Env (Code ONat) -> Code ONat
compArg (Var name) env = envLookup env name
compArg (Num n) env = MkONat n

compExp : Exp -> Env (Code ONat) -> (Env (Code ONat) -> Code ONat) -> Code ONat

// without copy propagation
// compExp (Val name arg) env cont = (r := Dbg (MkOString name) (compArg arg env) ; cont (envInsert env name r))

// with copy propagation
compExp (Val name (Var targetName)) env cont = (r  = Dbg (MkOString name) (envLookup env targetName) ; cont (envInsert env name r))
compExp (Val name (Num n)) env cont          = (r := Dbg (MkOString name) (MkONat n) ; cont (envInsert env name r))

// arith ops
compExp (Add name arg1 arg2) env cont = (r := Dbg (MkOString name) (AddOp (compArg arg1 env) (compArg arg2 env)) ; cont (envInsert env name r))
compExp (Mul name arg1 arg2) env cont = (r := Dbg (MkOString name) (MulOp (compArg arg1 env) (compArg arg2 env)) ; cont (envInsert env name r))

compile : List Exp -> Env (Code ONat) -> (Env (Code ONat) -> Code ONat) -> Code ONat
compile ListNil env cont = cont env
compile (ListCons exp l) env cont = compExp exp env (\env -> compile l env cont)


src = "x = 2 ; v1 = x ; v2 = v1 ; v3 = v2 ; v4 = v3 ; b = v4 ; y = x + 2 ; a = 12 ; z = y * b ; w = 12 * z ; q = w * 2 ;"

o0 = words " hello world! ; x = 1 "
o1 = words src
o2 = map isNumber o1

Tup2 : Type
MkT2 : {a b} -> a -> b -> Tup2

OTup2 :: Type
OMkT2 : {a b} -> a -> b -> Code OTup2

lastEntry : {a} -> Env a -> a
lastEntry (EntryEnv n v e) = v

//MkT2 o1 o2
ast = parse (words src)
result = MkT2 (MkT2 src ast) (eval ast EmptyEnv)

v = compile ast EmptyEnv lastEntry
//v = lastEntry (compile' ast EmptyEnv)
//v

// \s -> compiled_isNumberChar s
// \a b -> compiled_and a b
// \f s -> compiled_allCharIs f s
// \s -> compiled_reverseString s
// \s -> compiled_parseDigit s
// \s n -> compiled_parseNat_go s n
// \s -> compiled_parseNat s
// \a b -> compiled_parseArg a b
// \{m} a b c -> compiled_envInsert {m} a b c
// \{m} a b -> compiled_envLookup {m} a b
// \a b -> compiled_evalArg a b
// \a b -> compiled_evalExp a b
// \a b -> compiled_eval a b
// \l -> compiled_parse l

//eval ast EmptyEnv
//OMkT2 v result

//example
\src ->
  ( wl := compiled_words src
  ; ast := compiled_parse wl
  ; compiled_eval ast OEmptyEnv
  )



/*
  done - tokenizer
  done - parser
  done - compile time interpreter ; output each variable value
  - runtime interpreter
  done - strEq based List (Prod String Nat) as Env with linear time lookup
  - generate python or C via haskell_stage (backend.hs)
*/

/*
  Q: do we need strEq? i think yes!
  - pattern guard
*/

