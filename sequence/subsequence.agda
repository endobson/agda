{-# OPTIONS --cubical --safe --exact-split #-}

module sequence.subsequence where

open import base
open import hlevel.base
open import nat
open import order
open import order.instances.nat
open import sequence
open import truncation

isSubsequenceOf' : {ℓ : Level} {D : Type ℓ} (s₁ s₂ : Sequence D) -> Type ℓ
isSubsequenceOf' s₁ s₂ = Σ[ f ∈ (ℕ -> ℕ) ] ((∀ i -> f i < f (suc i)) × (∀ i -> s₁ (f i) == s₂ i))

isSubsequenceOf : {ℓ : Level} {D : Type ℓ} (s₁ s₂ : Sequence D) -> Type ℓ
isSubsequenceOf s₁ s₂ = ∥ isSubsequenceOf' s₁ s₂ ∥

isProp-isSubsequenceOf : ∀ {ℓ : Level} {D : Type ℓ} {s₁ s₂ : Sequence D} -> isProp (isSubsequenceOf s₁ s₂)
isProp-isSubsequenceOf = squash
