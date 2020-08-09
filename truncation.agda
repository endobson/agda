{-# OPTIONS --cubical --safe --exact-split #-}

module truncation where

open import base
open import equality
open import hlevel

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
    A B C : Type ℓ

data Squash (A : Type ℓ) : Type ℓ where
  ∣_∣ : A -> Squash A
  squash : (a b : Squash A) -> a == b

∥_∥ : Type ℓ -> Type ℓ
∥_∥ = Squash

unsquash : isProp A -> ∥ A ∥ -> A
unsquash h ∣ a ∣ = a
unsquash h (squash a b i) = h (unsquash h a) (unsquash h b) i

∥-map : (A -> B) -> ∥ A ∥ -> ∥ B ∥
∥-map f ∣ a ∣ = ∣ f a ∣
∥-map f (squash a1 a2 i) = (squash (∥-map f a1) (∥-map f a2) i)

-- Mere existence

∃ : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃ A B = ∥ Σ A B ∥

infix 2 ∃-syntax

∃-syntax : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
