{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.int where

open import additive-group
open import additive-group.instances.int
open import int
open import monoid

--TODO remove
Monoid-ℤ+ : Monoid ℤ
Monoid-ℤ+ = record
  { _∙_ = _ℤ+_
  ; ε = (int 0)
  ; ∙-assoc = +-assoc
  ; ∙-left-ε = +-left-zero
  ; ∙-right-ε = +-right-zero
  ; isSet-Domain = isSetInt
  }
