{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-integral-domain where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import integral-domain
open import order
open import ordered-additive-group
open import ordered-ring
open import ordered-semiring
open import relation
open import ring
open import semiring

private
  variable
    ℓD ℓ< ℓ≤ ℓ# : Level

module _ {D : Type ℓD} {D# : Rel D ℓ#} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {O : isLinearOrder D<}
         {R : Ring S AG} {A : isTightApartness D#}
         {{LOA : LinearlyOrderedAdditiveStr ACM O}}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{ALO : ApartLinearOrderStr A O}}
         {{ID : IntegralDomain R A}}
         where
  private
    instance
      IS = S
      IR = R
      IO = O
      IACM = ACM
      IAG = AG
      IA = A
    module ID = IntegralDomain ID

    LT = _<_

  abstract
    0<1 : LT 0# 1#
    0<1 = handle (eqInv <>-equiv-# ID.1#0)
      where
      handle : (1# < 0#) ⊎ (0# < 1#) -> 0# < 1#
      handle (inj-l 1<0) = bot-elim (1≮0 1<0)
      handle (inj-r 0<1) = 0<1


module _ {D : Type ℓD} {D# : Rel D ℓ#} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {O : isLinearOrder D<}
         {PO : isPartialOrder D≤}
         {R : Ring S AG} {A : isTightApartness D#}
         {{LOA : LinearlyOrderedAdditiveStr ACM O}}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{COS : CompatibleOrderStr O PO}}
         {{ALO : ApartLinearOrderStr A O}}
         {{ID : IntegralDomain R A}}
         where
  private
    instance
      IS = S
      IPO = PO
      IACM = ACM
    LTE = _≤_

  abstract
    0≤1 : LTE 0# 1#
    0≤1 = weaken-< 0<1
