{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.open-cover where

open import base
open import metric-space
open import subset
open import subset.subspace
open import truncation
open import rational
open import real

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  isMetricOpen : {ℓS : Level} (S : Subtype D ℓS) -> Type (ℓ-max ℓD ℓS)
  isMetricOpen S =
    ∀ ((x , _) : Subspace S) ->
    ∃[ ε ∈ ℚ ] (∀ (y : D) -> Real.U (distance x y) ε -> ⟨ S y ⟩)

  isCover : {ℓI ℓS : Level} {I : Type ℓI} (S : I -> Subtype D ℓS) -> Type (ℓ-max* 3 ℓI ℓD ℓS)
  isCover {I = I} S = ∀ (x : D) -> ∃[ i ∈ I ] ⟨ S i x ⟩

  isOpenCover : {ℓI ℓS : Level} {I : Type ℓI} (S : I -> Subtype D ℓS) -> Type (ℓ-max* 3 ℓI ℓD ℓS)
  isOpenCover {I = I} S = (∀ i -> isMetricOpen (S i)) × isCover S
