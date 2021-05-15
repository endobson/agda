{-# OPTIONS --cubical --safe --exact-split #-}

module maybe where

open import base

private
  variable
    ℓ : Level

data Maybe (A : Type ℓ) : Type ℓ where
 nothing : Maybe A
 just : A -> Maybe A
