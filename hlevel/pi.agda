{-# OPTIONS --cubical --safe --exact-split #-}

-- h-level for Π Types

module hlevel.pi where

open import base
open import equality
open import funext
open import hlevel.base

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A -> Type ℓ

-- isPropΠ is defined in hlevel.base since it doesn't need funExtPath and is needed
-- earlier on for meta hlevel constructions.

isOfHLevelΠ :
  (n : Nat) -> ((x : A) -> (isOfHLevel n (B x))) -> isOfHLevel n ((x : A) -> B x)
isOfHLevelΠ {A = A} {B = B} 0 h = (\x -> fst (h x)) , (\ f i y -> (snd (h y)) (f y) i)
isOfHLevelΠ {A = A} {B = B} 1 h f g i a = h a (f a) (g a) i
isOfHLevelΠ {A = A} {B = B} (suc (suc n)) h f g =
   subst (isOfHLevel (suc n)) funExtPath (isOfHLevelΠ (suc n) (\a -> h a (f a) (g a)))

isSetΠ : ((x : A) -> isSet (B x)) -> isSet ((x : A) -> (B x))
isSetΠ = isOfHLevelΠ 2