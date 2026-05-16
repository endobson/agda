{-# OPTIONS --cubical --safe --exact-split #-}

module group.int where

open import additive-group
open import additive-group.instances.int
open import base
open import equality
open import group
open import int.base
open import monoid.int

-- TODO move to group theory directory

GroupStr-ℤ+ : GroupStr ℤ
GroupStr-ℤ+ = record
  { monoid = Monoid-ℤ+
  ; inverse = -_
  ; ∙-left-inverse = +-commute >=> +-inverse
  ; ∙-right-inverse = +-inverse
  }

ℤ-Group : Group ℓ-zero
ℤ-Group = ℤ , GroupStr-ℤ+
