module Staging

data Polarity = Value | Computation

--%logging "staging" 1000
data Ty : Polarity -> Type where
  Arr : Value -> Ty p -> Computation
  -- user
  Int_ : Value
--%logging "staging" 0

{-
#Polarity    : Type
#Value       : Polarity
#Computation : Polarity

#Ty   : Polarity -> Type
#Arr  : Value -> Ty p -> Computation

#Code : Ty p -> Type
#PApp : {a : Value} -> {b : Ty p} -> Arr a b ->  a -> b
#PLam : {a : Value} -> {b : Ty p} -> (a -> b) -> Arr a b
#Let  : {a : Ty p}  -> {b : Ty q} -> a -> (a -> b) -> b
-}

data Code : Ty p -> Type where

  PApp : {a : Value} -> {b : Ty p} -> Arr a b -> a -> b
  PLam : {a : Value} -> {b : Ty p} -> (a -> b) -> Arr a b
  Let  : {a : Ty p} -> {b : Ty q} -> a -> (a -> b) -> b

  -- user
  One : Int_
  Mul : Int_ -> Int_ -> Int_

--%logging "staging" 1000
--%logging 1000
--%logging "elab"  1000

pow2_ : Int_
pow2_ = One

pow3_ : IO ()
pow3_ = do
  print "hello"
  let x = One
      y : Int_
      y = Mul x ?m
  pure ()
--%logging "staging" 0


half : Nat -> Maybe Nat
half Z = Just Z
half (S (S n)) with (half n)
  _ | Just k = Just (S k)
  _ | _ = Nothing
half _ = Nothing

sqr : Arr Int_ Int_
sqr = \c => Mul c c

pow_ : Nat -> Int_ -> Int_
pow_ Z     _ = One
pow_ (S Z) c = c
pow_ n c with (half n)
  pow_ n c | (Just k) = PApp sqr (pow_ k c)
  --pow_ n c | (Just k) = sqr (pow_ k c)
  pow_ (S n) c | _ = Mul c (pow_ n c)
  pow_ _ _ | _ = assert_total $ idris_crash "pow_"

main_ : Arr Int_ Int_
main_ = \c => pow_ 5 c

-- example2

%logging "staging" 1000
sqr2 : Arr Int_ Int_
sqr2 = \c => Mul c c

--sqr3 : Int_
--sqr3 = sqr2 One
%logging "staging" 0
