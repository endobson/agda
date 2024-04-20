{-# OPTIONS --cubical --safe --exact-split #-}

-- TODO change name
module nat.even-odd where

open import nat
open import equivalence
open import isomorphism
open import base
open import sum
open import hlevel
open import type-algebra
open import univalence
open import equality
open import additive-group
open import additive-group.instances.nat
open import semiring
open import semiring.instances.nat
open import div

-- Even/Odd

Even : (n : Nat) -> Type₀
Odd : (n : Nat) -> Type₀
Even zero = Top
Even (suc n) = Odd n
Odd zero = Bot
Odd (suc n) = Even n

OddEven : (n : Nat) -> Type₀
OddEven n = Odd n ⊎ Even n

abstract
  isContr-OddEven : (n : Nat) -> isContr (OddEven n)
  isContr-OddEven zero = inj-r tt , \{ (inj-l ()) ; (inj-r tt) -> refl }
  isContr-OddEven (suc n) = subst isContr (ua ⊎-flip-eq) (isContr-OddEven n)

isProp-Even : (n : Nat) -> isProp (Even n)
isProp-Odd : (n : Nat) -> isProp (Odd n)

isProp-Even zero = isPropTop
isProp-Even (suc n) = isProp-Odd n
isProp-Odd zero = isPropBot
isProp-Odd (suc n) = isProp-Even n

Even->¬Odd : (n : Nat) -> Even n -> ¬ (Odd n)
Even->¬Odd (suc n) en on = Even->¬Odd n on en

Odd->¬Even : (n : Nat) -> Odd n -> ¬ (Even n)
Odd->¬Even n on en = Even->¬Odd n en on

¬Odd->Even : (n : Nat) -> (¬ (Odd n)) -> Even n
¬Even->Odd : (n : Nat) -> (¬ (Even n)) -> Odd n

¬Odd->Even zero    _   = tt
¬Odd->Even (suc i) ¬ei = ¬Even->Odd i ¬ei

¬Even->Odd zero    ¬e  = (¬e tt)
¬Even->Odd (suc i) ¬oi = ¬Odd->Even i ¬oi

Odd≃¬Even : (n : Nat) -> Odd n ≃ ¬ (Even n)
Odd≃¬Even n = isoToEquiv (isProp->iso (Odd->¬Even n) (¬Even->Odd n) (isProp-Odd n) (isProp¬ _))

Even->div' : {n : Nat} -> Even n -> 2 div' n
Even->div' {zero} _ = (0 , refl)
Even->div' {suc zero} ()
Even->div' {suc (suc n)} e = case (Even->div' {n} e) of
  \ (i , p) -> suc i , cong (2 +_) p

div'->Even : {n : Nat} -> 2 div' n -> Even n
div'->Even (i , p) = subst Even p (handle i)
  where
  handle : (i : Nat) -> Even (i * 2)
  handle zero    = tt
  handle (suc i) = handle i

Even≃div' : {n : Nat} -> Even n ≃ (2 div' n)
Even≃div' {n} = isoToEquiv (isProp->iso Even->div' div'->Even (isProp-Even n) (isPropDiv'₁ 2⁺))

Odd≃¬div' : {n : Nat} -> Odd n ≃ ¬ (2 div' n)
Odd≃¬div' {n} = subst (\x -> Odd n ≃ ¬ x) (ua Even≃div') (Odd≃¬Even n)

sum-Odd-iso : (i j : Nat) -> Iso (Odd (i + j)) ((Odd i × Even j) ⊎ (Even i × Odd j))
sum-Even-iso : (i j : Nat) -> Iso (Even (i + j)) ((Even i × Even j) ⊎ (Odd i × Odd j))

sum-Odd-iso zero    j .Iso.fun oj                     = inj-r (tt , oj)
sum-Odd-iso zero    j .Iso.inv (inj-r (tt , oj))      = oj
sum-Odd-iso zero    j .Iso.leftInv  _                 = refl
sum-Odd-iso zero    j .Iso.rightInv (inj-r (tt , oj)) = refl
sum-Odd-iso (suc i) j = sum-Even-iso i j

sum-Even-iso zero    j .Iso.fun ej                     = inj-l (tt , ej)
sum-Even-iso zero    j .Iso.inv (inj-l (tt , ej))      = ej
sum-Even-iso zero    j .Iso.leftInv  _                 = refl
sum-Even-iso zero    j .Iso.rightInv (inj-l (tt , ej)) = refl
sum-Even-iso (suc i) j = sum-Odd-iso i j
