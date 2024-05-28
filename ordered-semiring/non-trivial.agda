{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.non-trivial where

open import additive-group
open import base
open import order
open import ordered-additive-group
open import ordered-semiring
open import relation
open import semiring
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<}
  where
  private
    instance
      IACM = ACM
      ILO = LO
      IS = S

  record NonTrivialLinearlyOrderedSemiringStr (LOS : LinearlyOrderedSemiringStr S LO) :
      Type (ℓ-max ℓD ℓ<)
    where
    no-eta-equality
    field
      0<1 : 0# < 1#

  module _ {LOS : LinearlyOrderedSemiringStr S LO} {{NTS : NonTrivialLinearlyOrderedSemiringStr LOS}}
    where
    open NonTrivialLinearlyOrderedSemiringStr NTS public

    module _ {{LOAS : LinearlyOrderedAdditiveStr ACM LO}} where
      opaque
        0<2 : 0# < 2#
        0<2 = +-preserves-0< 0<1 0<1

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {PO : isPartialOrder D≤}
  where
  private
    instance
      IACM = ACM
      IPO = PO
      IS = S

  record NonTrivialPartiallyOrderedSemiringStr (POS : PartiallyOrderedSemiringStr S PO) :
      Type (ℓ-max ℓD ℓ≤)
    where
    no-eta-equality
    field
      0≤1 : 0# ≤ 1#

  module _ {POS : PartiallyOrderedSemiringStr S PO} {{NTS : NonTrivialPartiallyOrderedSemiringStr POS}}
    where
    open NonTrivialPartiallyOrderedSemiringStr NTS public
