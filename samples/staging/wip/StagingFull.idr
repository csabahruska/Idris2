module Staging
data Polarity = Value | Computation

data Ty : Polarity -> Type where
  Arr : Ty Value -> Ty p -> Ty Computation
  -- user
  Int_ : Ty Value

data Code : Ty p -> Type where

  PApp : {a : Ty Value} -> {b : Ty p} -> Code (Arr a b) -> Code a -> Code b
  PLam : {a : Ty Value} -> {b : Ty p} -> (Code a -> Code b) -> Code (Arr a b)
  Let  : {a : Ty p} -> {b : Ty q} -> Code a -> (Code a -> Code b) -> Code b
  -- user
  One : Code Int_
  Mul : Code Int_ -> Code Int_ -> Code Int_

--pow_ : Int_


half : Nat -> Maybe Nat
half Z = Just Z
half (S (S n)) with (half n)
  _ | Just k = Just (S k)
  _ | _ = Nothing
half _ = Nothing

sqr : Code (Arr Int_ Int_)
sqr = PLam $ \c => Mul c c

pow_ : Nat -> Code Int_ -> Code Int_
--pow_ : Nat -> Int_ -> Int_
pow_ Z     _ = One
pow_ (S Z) c = c
pow_ n c with (half n)
  pow_ n c | (Just k) = PApp sqr (pow_ k c)
  pow_ (S n) c | _ = Mul c (pow_ n c)
  pow_ _ _ | _ = assert_total $ idris_crash "pow_"

main_ : Code (Arr Int_ Int_)
main_ = PLam $ \c => pow_ 5 c
