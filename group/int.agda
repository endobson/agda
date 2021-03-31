{-# OPTIONS --cubical --safe --exact-split #-}

module group.int where

open import int
open import equality
open import group
open import commutative-monoid.int

GroupStr-ℤ+ : GroupStr ℤ
GroupStr-ℤ+ = record
  { comm-monoid = CommMonoid-ℤ+
  ; inverse = -_
  ; ∙-left-inverse = +-commute >=> add-minus-zero
  }
