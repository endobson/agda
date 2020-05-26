{-# OPTIONS --cubical --safe --exact-split #-}

module truncation where

open import base
open import equality

private
  variable
    ℓ : Level
    A B C : Type ℓ

data Squash (A : Type ℓ) : Type ℓ where
  squash-inj : A -> Squash A
  squash : (a b : Squash A) -> a == b


data Suspension (A : Type ℓ) : Type ℓ where
  north : Suspension A
  south : Suspension A
  merid : (a : A) -> north == south
