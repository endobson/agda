{-# OPTIONS --cubical --safe --exact-split #-}

module discrete where

open import base
open import equality
open import functions
open import hlevel
open import relation
open import funext

private
  variable
    ℓ : Level
    A B : Type ℓ

Injective->Discrete : (f : A -> B) -> Injective f -> Discrete B -> Discrete A
Injective->Discrete f inj-f discB a1 a2 with (discB (f a1) (f a2))
... | (yes p) = yes (inj-f p)
... | (no ¬p) = no (\p -> ¬p (cong f p))

isProp-Discrete : isProp (Discrete A)
isProp-Discrete d1 = isPropΠ2 (\ a1 a2 -> isPropDec (Discrete->isSet d1 a1 a2)) d1
