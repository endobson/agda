{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.maximum where

open import base
open import commutative-monoid
open import equality
open import finite-commutative-monoid
open import finite-commutative-monoid.without-point
open import finset
open import order
open import order.minmax
open import order.minmax.commutative-monoid

module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<}
         {{Max : MaxOperationStr LO}}
         {{Min : GlobalMinOperationStr LO}}
         {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
  private
    instance
      ILO = LO

  finiteMax : (f : I -> D) -> D
  finiteMax f = finiteMerge MaxCommMonoid f

  module _ where
    private
      instance
        NLO = NegatedLinearOrder LO
    abstract
      finiteMax-≮ : (f : I -> D) -> (i : I) -> finiteMax f ≮ f i
      finiteMax-≮ f i = trans-≤-= max-≮-left (sym (finiteMerge-WithoutPoint _ i f))

  module _ {ℓ≤ : Level} {PO : PartialOrderStr D ℓ≤} {{CO : CompatibleOrderStr LO PO}} where
    private
      instance
        IPO = PO

    abstract
      finiteMax-≤ : (f : I -> D) -> (i : I) -> f i ≤ finiteMax f
      finiteMax-≤ f i = convert-≮ (finiteMax-≮ f i)
