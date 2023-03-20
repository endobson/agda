{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.int where

open import int
open import monoid

Monoid-ℤ+ : Monoid ℤ
Monoid-ℤ+ = record
  { _∙_ = _+_
  ; ε = (int 0)
  ; ∙-assoc = +-assoc
  ; ∙-left-ε = +-left-zero
  ; ∙-right-ε = +-right-zero
  ; isSet-Domain = isSetInt
  }
