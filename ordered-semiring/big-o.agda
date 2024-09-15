{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.big-o where

open import additive-group
open import base
open import order
open import order.minmax
open import ordered-additive-group.absolute-value
open import relation
open import semiring
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

  BigO' : (f g : I -> D) -> Type _
  BigO' f g = Σ[ k ∈ D ] Σ[ n ∈ I ] (∀ i -> n ≤ i -> abs (f i) ≤ (k * g i))

  BigO : (f g : I -> D) -> Type _
  BigO f g = ∥ BigO' f g ∥
