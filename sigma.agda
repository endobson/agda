{-# OPTIONS --cubical --safe --exact-split #-}

module sigma where

open import base

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : ∀ (A : Type ℓ₁) (B : A → Type ℓ₂) → Type (ℓ-max ℓ₁ ℓ₂)
Σ-syntax = Σ

syntax Σ-syntax A (\x -> B) = Σ[ x ∈ A ] B
