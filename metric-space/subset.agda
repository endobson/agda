{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.subset where

open import base
open import metric-space
open import metric-space.continuous
open import subset
open import relation
open import real.subspace
open import truncation hiding (Dense)

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  Dense : {ℓS : Level} -> Pred (Subtype D ℓS) (ℓ-max* 3 ℓ-one ℓD ℓS)
  Dense S = ∀ (x : D) (ε : ℝ⁺) -> ∃[ y ∈ D ] (εClose ε x y × ⟨ S y ⟩)
