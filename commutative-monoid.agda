{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid where

open import base
open import equality
open import functions
import monoid

record CommutativeMonoid {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    {{monoid}} : monoid.Monoid Domain
  open monoid.Monoid monoid public

  field
    ∙-commute : {m n : Domain} -> (m ∙ n) == (n ∙ m)
