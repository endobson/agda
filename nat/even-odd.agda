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
Even->¬Odd n en on =
  inj-l!=inj-r (isContr->isProp (isContr-OddEven n) (inj-l on) (inj-r en))

Odd->¬Even : (n : Nat) -> Odd n -> ¬ (Even n)
Odd->¬Even n on en = Even->¬Odd n en on

¬Even->Odd : (n : Nat) -> (¬ (Even n)) -> Odd n
¬Even->Odd zero          ¬e = bot-elim (¬e tt)
¬Even->Odd (suc zero)    _  = tt
¬Even->Odd (suc (suc n)) ¬e = ¬Even->Odd n ¬e

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
