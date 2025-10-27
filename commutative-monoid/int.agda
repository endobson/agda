{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid.int where

open import additive-group.instances.int
open import additive-group
open import commutative-monoid
open import int
open import monoid.int

-- TODO remove
CommMonoid-ℤ+ : CommMonoid ℤ
CommMonoid-ℤ+ = record
  { monoid = Monoid-ℤ+
  ; ∙-commute = +-commute
  }
