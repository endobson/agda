{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.cauchy where

open import base
open import metric-space
open import order
open import order.instances.nat
open import order.instances.real
open import real.subspace
open import sequence
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {{MS : MetricSpaceStr D}} where
  isCauchy : Sequence D -> Type ℓ-one
  isCauchy s =
    ∀ (ε : ℝ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁) (s m₂))

  isCauchy' : Sequence D -> Type ℓ-one
  isCauchy' s =
    ∀ (ε : ℝ⁺) -> ∀Largeℕ (\n -> (m : Nat) -> n ≤ m -> εClose ε (s n) (s m))

  opaque
    isCauchy->isCauchy' : {s : Sequence D} -> isCauchy s -> isCauchy' s
    isCauchy->isCauchy' cauchy ε =
      ∥-map (\ (n , f) -> n , \m₁ n≤m₁ m₂ m₁≤m₂ -> f m₁ m₂ n≤m₁ (trans-≤ n≤m₁ m₁≤m₂)) (cauchy ε)

    isCauchy'->isCauchy : {s : Sequence D} -> isCauchy' s -> isCauchy s
    isCauchy'->isCauchy {s} cauchy' ε = ∥-map handle (cauchy' ε)
      where
      handle : ∀Largeℕ' (\n -> (m : Nat) -> n ≤ m -> εClose ε (s n) (s m)) ->
               Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁) (s m₂))
      handle (n , f) = n , (\m₁ m₂ -> g m₁ m₂ (split-< m₁ m₂))
        where
        g : (m₁ m₂ : Nat) -> (m₁ < m₂ ⊎ m₂ ≤ m₁) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε (s m₁) (s m₂)
        g m₁ m₂ (inj-l m₁<m₂) n≤m₁ n≤m₂ = f m₁ n≤m₁ m₂ (weaken-< m₁<m₂)
        g m₁ m₂ (inj-r m₂≤m₁) n≤m₁ n≤m₂ = trans-=-< distance-commute (f m₂ n≤m₂ m₁ m₂≤m₁)
