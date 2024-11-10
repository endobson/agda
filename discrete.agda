{-# OPTIONS --cubical --safe --exact-split #-}

module discrete where

open import base
open import equality
open import functions
open import funext
open import hlevel.base
open import hlevel.decision
open import hlevel.hedberg
open import relation

private
  variable
    ℓ : Level
    A B : Type ℓ

Discrete : Type ℓ -> Type ℓ
Discrete A = (x y : A) -> Dec (x == y)

record Discrete' (A : Type ℓ) : Type ℓ where
  field
    f : Discrete A

decide-= : {{Discrete' A}} -> Discrete A
decide-= = Discrete'.f useⁱ

Discrete->isSet : Discrete A -> isSet A
Discrete->isSet d = Stable==->isSet (\ x y -> Dec->Stable (d x y))

isProp-Discrete : isProp (Discrete A)
isProp-Discrete d1 = isPropΠ2 (\ a1 a2 -> isPropDec (Discrete->isSet d1 a1 a2)) d1

isInjective->Discrete : (f : A -> B) -> isInjective f -> Discrete B -> Discrete A
isInjective->Discrete f inj-f discB a1 a2 with (discB (f a1) (f a2))
... | (yes p) = yes (inj-f p)
... | (no ¬p) = no (\p -> ¬p (cong f p))
