{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.cauchy where

open import base
open import metric-space
open import order
open import order.instances.nat
open import real.subspace
open import sequence
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {{MS : MetricSpaceStr D}} where
  isMetricCauchy : Sequence D -> Type ℓ-one
  isMetricCauchy s =
    ∀ (ε : ℝ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁) (s m₂))

  isMetricCauchy' : Sequence D -> Type ℓ-one
  isMetricCauchy' s =
    ∀ (ε : ℝ⁺) -> ∀Largeℕ (\n -> (m : Nat) -> n ≤ m -> εClose ε (s n) (s m))
