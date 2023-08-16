{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.negated where

open import additive-group
open import base
open import order
open import ordered-additive-group
open import relation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} (ACM : AdditiveCommMonoid D)
         (LO : isLinearOrder D<)
         where
  private
    instance
      IACM = ACM
      ILO = LO
      PO = isLinearOrder->isPartialOrder-≯ LO

  module _ {{LOA : LinearlyOrderedAdditiveStr ACM LO}} where

    PartiallyOrderedAdditiveStr-Negated : PartiallyOrderedAdditiveStr ACM PO
    PartiallyOrderedAdditiveStr-Negated = record
      { +₁-preserves-≤ = +₁-preserves-≤'
      }
      where
      +₁-preserves-≤' : {a b c : D} -> b ≤ c -> (a + b) ≤ (a + c)
      +₁-preserves-≤' c≮b ac<ab = c≮b (+₁-reflects-< ac<ab)
