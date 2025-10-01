{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.area.base where

open import base
open import order
open import order.instances.rational
open import rational
open import rational-geometry.region
open import rational-geometry.boxes.base
open import rational-geometry.boxes.area
open import real
open import truncation

_⊆_ : {ℓ₁ ℓ₂ : Level} -> Region ℓ₁ -> Region ℓ₂ -> Type (ℓ-max ℓ₁ ℓ₂)
r1 ⊆ r2 = ∀ p -> Region.contains r1 p -> Region.contains r2 p


module _ where

  record isInnerApproximation {ℓR ℓB : Level} (R : Region ℓR) (a : ℚ) (b : Boxes ℓB) : Type (ℓ-max ℓB ℓR) where
    field
      contains : Boxes.region b ⊆ R
      bounded : a ≤ boxes-area b


  record isOuterApproximation {ℓR ℓB : Level} (R : Region ℓR) (a : ℚ) (b : Boxes ℓB) : Type (ℓ-max ℓB ℓR) where
    field
      contains : R ⊆ Boxes.region b
      bounded : boxes-area b ≤ a


  record isArea {ℓ : Level} (R : Region ℓ) (a : ℝ) : Type (ℓ-max ℓ-one ℓ) where
    field
      inner : ∀ (q : ℚ) -> Real.L a q -> ∃[ b ∈ Boxes ℓ-zero ] (isInnerApproximation R q b)
      outer : ∀ (q : ℚ) -> Real.U a q -> ∃[ b ∈ Boxes ℓ-zero ] (isOuterApproximation R q b)


  AreaOf : {ℓ : Level} -> Region ℓ -> Type (ℓ-max ℓ-one ℓ)
  AreaOf R = Σ ℝ (isArea R)


  -- TODO move to another file
  sandwich-isArea : {ℓ₁ ℓ₂ ℓ₃ : Level}
    {R₁ : Region ℓ₁} {R₂ : Region ℓ₂} {R₃ : Region ℓ₃} {a : ℝ} ->
    R₁ ⊆ R₂ -> R₂ ⊆ R₃ -> isArea R₁ a -> isArea R₃ a -> isArea R₂ a
  sandwich-isArea {R₁ = R₁} {R₂} {R₃} {a} 1⊆2 2⊆3 a₁ a₃ = record
    { inner = \q l -> ∥-map convert-inner (isArea.inner a₁ q l)
    ; outer = \q u -> ∥-map convert-outer (isArea.outer a₃ q u)
    }
    where
    convert-inner : {q : ℚ} ->
      Σ (Boxes ℓ-zero) (isInnerApproximation R₁ q) ->
      Σ (Boxes ℓ-zero) (isInnerApproximation R₂ q)
    convert-inner (b , approx) = b , record
      { contains = \p c -> 1⊆2 p (isInnerApproximation.contains approx p c)
      ; bounded = isInnerApproximation.bounded approx
      }
    convert-outer : {q : ℚ} ->
      Σ (Boxes ℓ-zero) (isOuterApproximation R₃ q) ->
      Σ (Boxes ℓ-zero) (isOuterApproximation R₂ q)
    convert-outer (b , approx) = b , record
      { contains = \p c -> isOuterApproximation.contains approx p (2⊆3 p c)
      ; bounded = isOuterApproximation.bounded approx
      }
