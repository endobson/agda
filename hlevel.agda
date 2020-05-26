{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel where

open import base
open import equality

private
  variable
    ℓ : Level
    A B C : Type ℓ

-- Deifined in core
-- isContr : Type ℓ -> Type ℓ
-- isContr A = Σ[ x ∈ A ] ((y : A) -> x == y)

isProp : Type ℓ -> Type ℓ
isProp A = ∀ (x y : A) -> x == y

isSet : Type ℓ -> Type ℓ
isSet A = ∀ (x y : A) -> isProp (x == y)
