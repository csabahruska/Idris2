import Data.String

data Arg : Type where
  Num : Nat -> Arg
  Var : String -> Arg

data Exp : Type where
  Val : String -> Arg -> Exp
  Add : String -> Arg -> Arg -> Exp
  Mul : String -> Arg -> Arg -> Exp

%hide Prelude.List

data List : Type -> Type where
  ListCons  : {a : _} -> a -> List a -> List a
  ListNil   : {a : _} -> List a

map : {a : _} -> {b : _} -> (a -> b) -> List a -> List b
map f ListNil = ListNil
map f (ListCons e es) = ListCons (f e) (map f es)

words_collect : String -> String -> List String
words_skip : String -> List String
words : String -> List String

words s = words_skip s

--strUncons : String -> Maybe (Char, String)

words_skip s = case strUncons s of
  Nothing         => ListNil
  Just (' ', cs)  => words_skip cs
  Just (c, cs)    => words_collect (singleton c) cs

words_collect w s = case strUncons s of
  Nothing         => ListCons w ListNil
  Just (' ', cs)  => ListCons w (words_skip cs)
  Just (c , cs)    => words_collect (w ++ singleton c) cs

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

allCharIs : (String -> Bool) -> String -> Bool
allCharIs f a = case strUncons a of
  Nothing       => True
  Just (c, s)   => (f $ singleton c) && (allCharIs f s)

isNumber : String -> Bool
isNumber s = allCharIs isNumberChar s

toCharList : String -> List String
toCharList s = case strUncons s of
  Nothing     => ListNil
  Just (a, b) => ListCons (singleton a) (toCharList b)

reverseString : String -> String
reverseString s = case strUncons s of
  Nothing     => ""
  Just (c, s) => reverseString s ++ singleton c

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
parseDigit _   = ?partial1

parseNat_go : String -> Nat -> Nat
parseNat_go a n = case strUncons a of
  Nothing     => 0
  Just (c, s) => plus (mult n (parseDigit $ singleton c)) (parseNat_go s (mult n 10))

parseNat : String -> Nat
parseNat s = parseNat_go (reverseString s) 1

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

evalExp : Exp -> Env Nat -> Env Nat
evalExp (Val name arg) env = envInsert env name (evalArg arg env)
evalExp (Add name arg1 arg2) env = envInsert env name (plus (evalArg arg1 env) (evalArg arg2 env))
evalExp (Mul name arg1 arg2) env = envInsert env name (mult (evalArg arg1 env) (evalArg arg2 env))

eval : List Exp -> Env Nat -> Env Nat
eval ListNil env = env
eval (ListCons exp l) env = eval l (evalExp exp env)

src : String
src = "x = 2 ; v1 = x ; v2 = v1 ; v3 = v2 ; v4 = v3 ; b = v4 ; y = x + 2 ; a = 12 ; z = y * b ; w = 12 * z ; q = w * 2 ;"

result : ?
result =
  let ast = parse (words src) in (src, ast, eval ast EmptyEnv)

{-
  TODO:
  - use idris primitive types and ops, Char, String, Nat
  - staging: use HiCal as object language
-}
