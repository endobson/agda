{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.minmax where

open import additive-group
open import base
open import equality
open import order
open import order.minmax
open import truncation
open import hlevel.base
open import semiring
open import ordered-semiring
open import ordered-ring

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM}
         {LO : LinearOrderStr D ℓ<}
         {PO : PartialOrderStr D ℓ≤}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{CO : CompatibleOrderStr LO PO}}
  where
  private
    instance
      ILO = LO
      IPO = PO
      IACM = ACM
      IS = S

  -- TODO (add similar proofs for min)

  module _ {{Max : MaxOperationStr LO}} where
    abstract
      *-distrib-max-left : {a b c : D} -> 0# ≤ a -> a * max b c == max (a * b) (a * c)
      *-distrib-max-left {a} {b} {c} 0≤a = antisym-≤ (convert-≮ abac≮abc) abac≤abc
        where
        b≤bc : b ≤ max b c
        b≤bc = max-≤-left
        c≤bc : c ≤ max b c
        c≤bc = max-≤-right
        ab≤abc : (a * b) ≤ (a * max b c)
        ab≤abc = *₁-preserves-≤ 0≤a b≤bc
        ac≤abc : (a * c) ≤ (a * max b c)
        ac≤abc = *₁-preserves-≤ 0≤a c≤bc
        abac≤abc : (max (a * b) (a * c)) ≤ (a * max b c)
        abac≤abc = max-least-≤ ab≤abc ac≤abc
        abac≮abc : (max (a * b) (a * c)) ≮ (a * max b c)
        abac≮abc abac<abc = irrefl-< (max-least-< b<bc c<bc)
          where
          ab<abc : (a * b) < (a * (max b c))
          ab<abc = trans-≤-< max-≤-left abac<abc
          ac<abc : (a * c) < (a * (max b c))
          ac<abc = trans-≤-< max-≤-right abac<abc
          a≮0 : a ≮ 0#
          a≮0 = convert-≤ 0≤a
          b<bc : b < max b c
          b<bc = *₁-reflects-< a≮0 ab<abc
          c<bc : c < max b c
          c<bc = *₁-reflects-< a≮0 ac<abc

  module _ {{Max : MaxOperationStr LO}} {{Min : MinOperationStr LO}} where
    abstract
      *-distrib-flip-max-left : {a b c : D} -> a ≤ 0# -> a * max b c == min (a * b) (a * c)
      *-distrib-flip-max-left {a} {b} {c} a≤0 = antisym-≤ abc≤abac (convert-≮ abc≮abac)
        where
        b≤bc : b ≤ max b c
        b≤bc = max-≤-left
        c≤bc : c ≤ max b c
        c≤bc = max-≤-right
        abc≤ab : (a * max b c) ≤ (a * b)
        abc≤ab = *₁-flips-≤ a≤0 b≤bc
        abc≤ac : (a * max b c) ≤ (a * c)
        abc≤ac = *₁-flips-≤ a≤0 c≤bc
        abc≤abac : (a * max b c) ≤ min (a * b) (a * c)
        abc≤abac = min-greatest-≤ abc≤ab abc≤ac
        abc≮abac : (a * max b c) ≮ min (a * b) (a * c)
        abc≮abac abc<abac = irrefl-< (max-least-< b<bc c<bc)
          where
          abc<ab : (a * (max b c)) < (a * b)
          abc<ab = trans-<-≤ abc<abac min-≤-left
          abc<ac : (a * (max b c)) < (a * c)
          abc<ac = trans-<-≤ abc<abac min-≤-right
          0≮a : 0# ≮ a
          0≮a = convert-≤ a≤0
          b<bc : b < max b c
          b<bc = *₁-flip-reflects-< 0≮a abc<ab
          c<bc : c < max b c
          c<bc = *₁-flip-reflects-< 0≮a abc<ac
