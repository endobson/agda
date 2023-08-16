{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.absolute-value where

open import additive-group
open import base
open import equality
open import finite-commutative-monoid
open import finset
open import finsum
open import finsum.arithmetic
open import finsum.order
open import functions
open import order
open import order.minmax
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import relation

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{Max : MaxOperationStr LO}} {{CO : CompatibleOrderStr LO PO}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
         where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = PO

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    private
      finiteSum-abs-bounded : {f : I -> D} ->
        ((- (finiteSum (abs ∘ f))) ≤ finiteSum f) ×
        (finiteSum f ≤ finiteSum (abs ∘ f))
      finiteSum-abs-bounded =
        trans-=-≤
          (sym finiteSum--)
          (finiteSum-preserves-≤ (\i -> trans-≤-= (minus-flips-≤ max-≤-right) minus-double-inverse)) ,
        finiteSum-preserves-≤ (\i -> abs-≤)

    abstract
      finiteSum-abs≤ : {f : I -> D} -> abs (finiteSum f) ≤ finiteSum (abs ∘ f)
      finiteSum-abs≤ =
        max-least-≤ (proj₂ finiteSum-abs-bounded)
                    (trans-≤-= (minus-flips-≤ (proj₁ finiteSum-abs-bounded)) minus-double-inverse)
