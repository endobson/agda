{-# OPTIONS --cubical --safe --exact-split #-}

module real.metric-space.totally-bounded where

open import base
open import metric-space
open import metric-space.instances.subspace
open import metric-space.instances.real
open import metric-space.open-cover
open import metric-space.bounded
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

private
  -- This should be in generic metric space code
  module _ {ℓS₁ ℓS₂ ℓB : Level} {S₁ : Subtype ℝ ℓS₁} {S₂ : Subtype ℝ ℓS₂}
           (S₁⊆S₂ : ∀ x -> ⟨ S₁ x ⟩ -> ⟨ S₂ x ⟩)
           (isTotallyBounded-S₂ : isTotallyBounded (Subspace S₂) ℓB)
           (magic : Magic)
    where
    isTotallyBounded-⊆ : isTotallyBounded (Subspace S₁) ℓB
    isTotallyBounded-⊆ = record { cover = cover }
      where
      cover :
        ∀ ((ε , _) : ℝ⁺) -> ∃[ n ∈ ℕ ] Σ[ C ∈ (Fin n -> Subtype (Subspace S₁) ℓB) ]
          (isOpenCover C ×
           ∀ i -> (x₁ x₂ : Subspace (C i)) -> distance x₁ x₂ < ε)
      cover ε⁺@(ε , _) = ∥-map handle (isTotallyBoundedᵉ.cover isTotallyBounded-S₂ ε⁺)
        where
        handle :
          Σ[ n ∈ ℕ ] Σ[ C ∈ (Fin n -> Subtype (Subspace S₂) ℓB) ]
            (isOpenCover C ×
             ∀ i -> (x₁ x₂ : Subspace (C i)) -> distance x₁ x₂ < ε) ->
          Σ[ n ∈ ℕ ] Σ[ C ∈ (Fin n -> Subtype (Subspace S₁) ℓB) ]
            (isOpenCover C ×
             ∀ i -> (x₁ x₂ : Subspace (C i)) -> distance x₁ x₂ < ε)
        handle (n , C , (isOpen-C , isCover-C) , bounded) = n , C' , isOpenCover-C' , bounded'
          where
          C' : Fin n -> Subtype (Subspace S₁) ℓB
          C' i (x , S₁x) = C i (x , S₁⊆S₂ x S₁x)

          isOpen-C' : ∀ i -> isMetricOpen (C' i)
          isOpen-C' i ((x , S₁x) , Cx) = magic


          isOpenCover-C' : isOpenCover C'
          isOpenCover-C' = isOpen-C' , magic

          bounded' : ∀ i -> (x₁ x₂ : Subspace (C' i)) -> distance x₁ x₂ < ε
          bounded' i ((x₁ , S₁x₁) , Cx₁) ((x₂ , S₁x₂) , Cx₂) =
            bounded i ((x₁ , S₁⊆S₂ x₁ S₁x₁) , Cx₁) ((x₂ , S₁⊆S₂ x₂ S₁x₂) , Cx₂)




{-
  module _ {ℓS : Level} {S : Subtype ℝ ℓS}
           (isBounded-S : isBounded (Subspace S))
           ((x , Sx) : Subspace S)
    where
    isBounded+element->isTotallyBounded : isTotallyBounded (Subspace S) ℓ-zero
    isBounded+element->isTotallyBounded = ?


module _ {ℓS : Level} {S : Subtype ℝ ℓS}
         (isBounded-S : isBounded (Subspace S))
         (isInhabited-S : ∥ Subspace S ∥)
  where
  isBounded+isInhabited->isTotallyBounded : isTotallyBounded (Subspace S) ℓ-zero
  isBounded+isInhabited->isTotallyBounded = ?
-}
