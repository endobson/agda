{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.negated-equivalence where

open import additive-group
open import base
open import equality
open import equivalence
open import finite-commutative-monoid
open import finset
open import finsum
open import finsum.arithmetic
open import funext
open import order
open import ordered-additive-group
open import relation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}}
         {LO : isLinearOrder D<} {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
  where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = isLinearOrder->isPartialOrder-≯ LO
      ICO = CompatibleNegatedLinearOrder LO

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    opaque
      finiteSum-negated-equivalence :
        (eq : I ≃ I) {f : I -> D} -> (∀ i -> f (eqFun eq i) == - (f i)) ->
        finiteSum f == 0#
      finiteSum-negated-equivalence eq {f} p = antisym-≤ lt2 lt1
        where
        path1 : finiteSum f == - finiteSum f
        path1 = finiteMerge-convert _ eq f >=>
                cong finiteSum (funExt p) >=>
                finiteSum--

        path2 : finiteSum f + finiteSum f == 0#
        path2 = +-right path1 >=> +-inverse

        lt1 : 0# ≤ finiteSum f
        lt1 f<0 = irrefl-path-< path2 (+-preserves-<0 f<0 f<0)
        lt2 : finiteSum f ≤ 0#
        lt2 0<f = irrefl-path-< (sym path2) (+-preserves-0< 0<f 0<f)
