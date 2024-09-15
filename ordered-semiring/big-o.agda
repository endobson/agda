{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.big-o where

open import additive-group
open import base
open import order
open import order.minmax
open import ordered-additive-group.absolute-value
open import relation
open import semiring
open import subset
open import subset.subspace
open import truncation

module _ {ℓI ℓD ℓI≤ ℓD≤ ℓD< : Level} {I : Type ℓI} {D : Type ℓD}
         {I≤ : Rel I ℓI≤} {D≤ : Rel D ℓD≤} {D< : Rel D ℓD<}
         {{IPO : isPartialOrder I≤}}
         {{DPO : isPartialOrder D≤}} {DLO : isLinearOrder D<}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
         {{AG : AdditiveGroup ACM}}
         {{Max : MaxOperationStr DLO}} where
  private
    instance
      I-DLO = DLO
      I-S = S
      I-ACM = ACM

    D⁺S : Subtype D ℓD<
    D⁺S d = 0# < d , isProp-<

    D⁺ : Type (ℓ-max ℓD ℓD<)
    D⁺ = Subspace D⁺S

  BigO' : (f g : I -> D) -> Type _
  BigO' f g = Σ[ (k , _) ∈ D⁺ ] Σ[ n ∈ I ] (∀ i -> n ≤ i -> abs (f i) ≤ (k * g i))

  BigO : (f g : I -> D) -> Type _
  BigO f g = ∥ BigO' f g ∥
