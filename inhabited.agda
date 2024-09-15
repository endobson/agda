{-# OPTIONS --cubical --safe --exact-split #-}

module inhabited where

open import base
open import truncation

private
  variable
    ℓD : Level

record InhabitedStr (D : Type ℓD) : Type ℓD where
  field
    elem : ∥ D ∥

inhabitedᵉ : (D : Type ℓD) -> {{InhabitedStr D}} -> ∥ D ∥
inhabitedᵉ D = InhabitedStr.elem useⁱ
