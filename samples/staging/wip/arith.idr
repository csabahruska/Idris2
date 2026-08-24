data Polarity = Value | Computation

data Ty : Polarity -> Type where
  Arr : Ty Value -> Ty p -> Ty Computation

  Prod : Ty Value -> Ty Value -> Ty Value
  Unit : Ty Value

  -- user
  Int_ : Ty Value

data Code : Ty p -> Type where

  PApp : {a : Ty Value} -> {b : Ty p} -> Code (Arr a b) -> Code a -> Code b
  PLam : {a : Ty Value} -> {b : Ty p} -> (Code a -> Code b) -> Code (Arr a b)
  Let  : {a : Ty p} -> {b : Ty q} -> Code a -> (Code a -> Code b) -> Code b
  -- user
  One : Code Int_
  Mul : Code Int_ -> Code Int_ -> Code Int_

  TT : Code Unit
  Pair : {a : Ty Value} -> {b : Ty Value} -> Code a -> Code b -> Code (Prod a b)
  Fst : {a : Ty Value} -> {b : Ty Value} -> Code (Prod a b) -> Code a
  Snd : {a : Ty Value} -> {b : Ty Value} -> Code (Prod a b) -> Code b

{-
// Backend primitives
OString :: Type
MkOString : String -> Code OString

ONat :: Type
MkONat : Nat -> Code ONat

AddOp   :: ONat -> ONat -> ONat
MulOp   :: ONat -> ONat -> ONat

Dbg :: OString -> ONat -> ONat

MatchSuc : {a} -> Code ONat -> Code a -> (Code ONat -> Code a) -> Code a

OArg :: Type
ONum :: ONat -> OArg
OVar :: OString -> OArg

OExp :: Type
OVal :: OString -> OArg -> OExp
OAdd :: OString -> OArg -> OArg -> OExp
OMul :: OString -> OArg -> OArg -> OExp
-}

{-
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
-}
