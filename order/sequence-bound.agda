{-# OPTIONS --cubical --safe --exact-split #-}

module order.sequence-bound where

open import order
open import order.instances.nat
open import base
open import nat
open import sequence
open import truncation


module _
  {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {{LO : isLinearOrder D<}}
  where

  record isLimitSuperior (s : ℕ -> D) (l : D) : Type (ℓ-max ℓD ℓ<) where
    field
      upper-bound : ∀ l₂ -> l < l₂ -> ∀Largeℕ (\i -> s i < l₂)
      tight : ∀ l₂ -> l₂ < l -> ∀ n₁ -> ∃[ n₂ ∈ ℕ ] ((n₁ < n₂) × (l₂ < s n₂))
