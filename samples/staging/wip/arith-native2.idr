import Data.String
import Data.Maybe

data Arg : Type where
  Num : Nat -> Arg
  Var : String -> Arg

data Exp : Type where
  Val : String -> Arg -> Exp
  Add : String -> Arg -> Arg -> Exp
  Mul : String -> Arg -> Arg -> Exp

parseNat : String -> Nat
parseNat s = case parsePositive s of
  Just n => n
  _ => ?partial1

isNumber : String -> Bool
isNumber s = isJust $ parseNumWithoutSign (unpack s) 0

parseArg : String -> Arg
parseArg arg = if isNumber arg then Num (parseNat arg) else Var arg


parse : List String -> List Exp
parse (name :: "=" :: arg :: ";" :: s) = Val name (parseArg arg) :: parse s
parse (name :: "=" :: arg1 :: "+" :: arg2 :: ";" :: s) = Add name (parseArg arg1) (parseArg arg2) :: parse s
parse (name :: "=" :: arg1 :: "*" :: arg2 :: ";" :: s) = Mul name (parseArg arg1) (parseArg arg2) :: parse s
parse x = Nil

data Env : Type -> Type where
  EmptyEnv : {a : _} -> Env a
  EntryEnv : {a : _} -> String -> a -> Env a -> Env a

envLookup : {a : _} -> Env a -> String -> a
envLookup (EntryEnv n v e) name = if (n == name) then v else (envLookup e name)
envLookup _ _ = ?partial2

envInsert : {a : _} -> Env a -> String -> a -> Env a
envInsert e name value = EntryEnv name value e

evalArg : Arg -> Env Nat -> Nat
evalArg (Var name) env = envLookup env name
evalArg (Num n) env = n

plusOp : Nat -> Nat -> Nat
multOp : Nat -> Nat -> Nat

evalExp : Exp -> Env Nat -> Env Nat
evalExp (Val name arg) env = envInsert env name (evalArg arg env)
evalExp (Add name arg1 arg2) env = envInsert env name (plusOp (evalArg arg1 env) (evalArg arg2 env))
evalExp (Mul name arg1 arg2) env = envInsert env name (multOp (evalArg arg1 env) (evalArg arg2 env))

eval : List Exp -> Env Nat -> Env Nat
eval Nil env = env
eval (exp :: l) env = eval l (evalExp exp env)

src : String
src = "x = 2 ; v1 = x ; v2 = v1 ; v3 = v2 ; v4 = v3 ; b = v4 ; y = x + 2 ; a = 12 ; z = y * b ; w = 12 * z ; q = w * 2 ;"

result : ?
result =
  let ast = parse (words src) in (src, ast, eval ast EmptyEnv)

{-
  TODO:
  - use idris primitive types and ops, Char, String, Nat
  - staging: use HiCal as object language
  - turn interpreter to compiler by controlling evaluation
    METHOD:
      A) 2ltt object language ; <-- start with this, because this is known
      B) elab reflection or undefined, stucks elab
-}
