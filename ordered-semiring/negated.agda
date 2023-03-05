{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.negated where

open import additive-group
open import base
open import order
open import ordered-semiring
open import semiring
open import sum

module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM)
         (LO : LinearOrderStr D ℓ<)
         where
  private
    instance
      IACM = ACM
      IS = S
      ILO = LO

      PO : PartialOrderStr D ℓ<
      PO = NegatedLinearOrder LO

  module _ {{LOS : LinearlyOrderedSemiringStr S LO}} where
    PartiallyOrderedSemiringStr-Negated : PartiallyOrderedSemiringStr S PO
    PartiallyOrderedSemiringStr-Negated = record
      { *₁-preserves-≤ = *₁-preserves-≮
      }

    StronglyPartiallyOrderedSemiringStr-Negated : StronglyPartiallyOrderedSemiringStr S LO PO
    StronglyPartiallyOrderedSemiringStr-Negated = record
      { *₁-reflects-≤      = *₁-reflects-≤'
      ; *₁-flip-reflects-≤ = *₁-flip-reflects-≤'
      }
      where
      *₁-reflects-≤' : {a b c : D} -> 0# < a -> (a * b) ≤ (a * c) -> b ≤ c
      *₁-reflects-≤' 0<a ac≮ab c<b = ac≮ab (*₁-preserves-< 0<a c<b)
      *₁-flip-reflects-≤' : {a b c : D} -> a < 0# -> (a * b) ≤ (a * c) -> c ≤ b
      *₁-flip-reflects-≤' a<0 ac≮ab b<c = ac≮ab (*₁-flips-< a<0 b<c)
