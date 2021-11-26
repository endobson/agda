{-# OPTIONS --cubical --safe --exact-split #-}

module polynomial where

open import base

data Poly {ℓ : Level} (X : Type ℓ) : Type ℓ where
  poly-const : (x : X) -> Poly X
