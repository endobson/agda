{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.negated where

open import additive-group
open import base
open import order
open import ordered-additive-group

module _ {ℓD ℓ< : Level} {D : Type ℓD} (ACM : AdditiveCommMonoid D)
         (LO : LinearOrderStr D ℓ<)
         where
  private
    instance
      IACM = ACM
      ILO = LO

      PO : PartialOrderStr D ℓ<
      PO = NegatedLinearOrder LO

  module _ {{LOA : LinearlyOrderedAdditiveStr ACM LO}} where

    PartiallyOrderedAdditiveStr-Negated : PartiallyOrderedAdditiveStr ACM PO
    PartiallyOrderedAdditiveStr-Negated = record
      { +₁-preserves-≤ = +₁-preserves-≤'
      }
      where
      +₁-preserves-≤' : {a b c : D} -> b ≤ c -> (a + b) ≤ (a + c)
      +₁-preserves-≤' c≮b ac<ab = c≮b (+₁-reflects-< ac<ab)
