{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid.int where

open import int
open import commutative-monoid
open import monoid.int

-- TODO remove
CommMonoid-ℤ+ : CommMonoid ℤ
CommMonoid-ℤ+ = record
  { monoid = Monoid-ℤ+
  ; ∙-commute = ℤ+-commute
  }
