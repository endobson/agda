{-# OPTIONS --cubical --safe --exact-split #-}

module group.int where

open import int
open import equality
open import group
open import monoid.int

-- TODO remove
GroupStr-ℤ+ : GroupStr ℤ
GroupStr-ℤ+ = record
  { monoid = Monoid-ℤ+
  ; inverse = ℤ-_
  ; ∙-left-inverse = ℤ+-commute >=> add-minus-zero
  ; ∙-right-inverse = add-minus-zero
  }
