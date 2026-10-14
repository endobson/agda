{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.bounded where

open import base
open import metric-space
open import metric-space.instances.subspace
open import metric-space.open-cover
open import truncation
open import rational
open import rational.order
open import real
open import real.subspace
open import nat
open import fin
open import subset
open import subset.subspace
open import real.rational
open import order
open import order.instances.real

module _ {ℓD : Level} {D : Type ℓD} (MS : MetricSpaceStr D) where
  private
    instance
      IMS = MS

  record isBoundedᵉ : Type ℓD where
    field
      boundℚ : ∃[ r ∈ ℚ ] ∀ (x₁ x₂ : D) -> Real.U (distance x₁ x₂) r

    opaque
      bound : ∃[ r ∈ ℝ ] ∀ (x₁ x₂ : D) -> (distance x₁ x₂) < r
      bound = ∥-map (\ (r , f) -> (ℚ->ℝ r , \ x₁ x₂ -> U->ℝ< (f x₁ x₂))) boundℚ


  record isTotallyBoundedᵉ (ℓ : Level) : Type (ℓ-max (ℓ-suc ℓ) ℓD) where
    field
      cover :
        ∀ ((ε , _) : ℝ⁺) -> ∃[ n ∈ ℕ ] Σ[ S ∈ (Fin n -> Subtype D ℓ) ]
          (isOpenCover S ×
           ∀ i -> (x₁ x₂ : Subspace (S i)) -> distance x₁ x₂ < ε)

isBounded : {ℓD : Level} (D : Type ℓD) {{MS : MetricSpaceStr D}} -> Type ℓD
isBounded D {{MS}} = isBoundedᵉ MS


isTotallyBounded : {ℓD : Level} (D : Type ℓD) {{MS : MetricSpaceStr D}} ->
                   (ℓ : Level) -> Type (ℓ-max (ℓ-suc ℓ) ℓD)
isTotallyBounded D {{MS}} = isTotallyBoundedᵉ MS
