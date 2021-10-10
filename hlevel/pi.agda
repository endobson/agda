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
    A A1 A2 A3 : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> B a -> Type ℓ

-- isPropΠ is defined in hlevel.base since it doesn't need funExtPath and is needed
-- earlier on for meta hlevel constructions.

isOfHLevelΠ :
  (n : Nat) -> ((x : A) -> (isOfHLevel n (B x))) -> isOfHLevel n ((x : A) -> B x)
isOfHLevelΠ {A = A} {B = B} 0 h = (\x -> fst (h x)) , (\ f i y -> (snd (h y)) (f y) i)
isOfHLevelΠ {A = A} {B = B} 1 h f g i a = h a (f a) (g a) i
isOfHLevelΠ {A = A} {B = B} (suc (suc n)) h f g =
   subst (isOfHLevel (suc n)) funExtPath (isOfHLevelΠ (suc n) (\a -> h a (f a) (g a)))

isContrΠ : ((x : A) -> isContr (B x)) -> isContr ((x : A) -> (B x))
isContrΠ = isOfHLevelΠ 0

isContrΠ2 : ((x : A) -> (y : B x) -> isContr (C x y)) -> isContr ((x : A) -> (y : B x) -> C x y)
isContrΠ2 h = isContrΠ (\a -> isContrΠ (h a))

isSetΠ : ((x : A) -> isSet (B x)) -> isSet ((x : A) -> (B x))
isSetΠ = isOfHLevelΠ 2

isSetΠ2 : ((x : A) -> (y : B x) -> isSet (C x y)) -> isSet ((x : A) -> (y : B x) -> (C x y))
isSetΠ2 h = isSetΠ (\a -> (isSetΠ (h a)))

-- Non dependent contractible function spaces can be reordered

isContrFun⁻ : isContr (A1 -> A2) -> A1 -> isContr A2
isContrFun⁻ (f , f') a1 = f a1 , \a2 i -> f' (\_ -> a2) i a1

isContrFun2⁻ : isContr (A1 -> A2 -> A3) -> A1 -> A2 -> isContr A3
isContrFun2⁻ h a1 = isContrFun⁻ (isContrFun⁻ h a1)
