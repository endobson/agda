{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain.apart-linear-order where

open import additive-group
open import base
open import integral-domain
open import ring
open import order
open import ordered-semiring
open import ordered-additive-group
open import semiring

module _ {ℓ ℓ< : Level} {D : Type ℓ}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         (R : Ring S AG)
         (LO : LinearOrderStr D ℓ<)
         {{LOS : LinearlyOrderedAdditiveStr ACM LO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
         where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S
      ILO = LO
      TA = (LinearOrderTightApartnessStr LO)

  -- We only have integral domains for non trivial rings
  IntegralDomain-LinearOrderStr : (0# < 1#) -> IntegralDomain R TA
  IntegralDomain-LinearOrderStr 0<1 = record
    { 1#0 = inj-r 0<1
    ; diff-#-equiv = diff-<>-equiv
    ; *-#0-equiv = *-<>0-equiv
    }
