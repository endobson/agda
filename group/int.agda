{-# OPTIONS --cubical --safe --exact-split #-}

module group.int where

open import additive-group.instances.int
open import additive-group
open import int
open import equality
open import group
open import monoid.int

-- TODO remove
GroupStr-ℤ+ : GroupStr ℤ
GroupStr-ℤ+ = record
  { monoid = Monoid-ℤ+
  ; inverse = -_
  ; ∙-left-inverse = +-commute >=> +-inverse
  ; ∙-right-inverse = +-inverse
  }
