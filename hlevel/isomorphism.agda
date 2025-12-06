{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.isomorphism where

open import base
open import hlevel.base
open import hlevel.retract
open import isomorphism.base

private
  variable
    ℓ : Level
    A₁ A₂ : Type ℓ

opaque
  iso-isOfHLevel : Iso A₁ A₂ -> (n : Nat) -> isOfHLevel n A₁ -> isOfHLevel n A₂
  iso-isOfHLevel i n = isOfHLevel-Retract n inv fun rightInv
    where
    open Iso i

  iso-isContr : Iso A₁ A₂ -> isContr A₁ -> isContr A₂
  iso-isContr i = iso-isOfHLevel i 0

  iso-isProp : Iso A₁ A₂ -> isProp A₁ -> isProp A₂
  iso-isProp i = iso-isOfHLevel i 1

  iso-isSet : Iso A₁ A₂ -> isSet A₁ -> isSet A₂
  iso-isSet i = iso-isOfHLevel i 2
