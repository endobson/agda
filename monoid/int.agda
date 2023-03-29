{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.int where

open import int
open import monoid

--TODO remove
Monoid-ℤ+ : Monoid ℤ
Monoid-ℤ+ = record
  { _∙_ = _ℤ+_
  ; ε = (int 0)
  ; ∙-assoc = ℤ+-assoc
  ; ∙-left-ε = ℤ+-left-zero
  ; ∙-right-ε = ℤ+-right-zero
  ; isSet-Domain = isSetInt
  }
