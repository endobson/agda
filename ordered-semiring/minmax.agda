{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.minmax where

open import additive-group
open import base
open import equality
open import hlevel.base
open import order
open import order.minmax
open import ordered-ring
open import ordered-semiring
open import relation
open import semiring
open import truncation

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}}
         {{LO : isLinearOrder D<}}
         {{PO : isPartialOrder D≤}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{CO : CompatibleOrderStr LO PO}}
  where

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

      *-distrib-max-right : {a b c : D} -> 0# ≤ a -> max b c * a == max (b * a) (c * a)
      *-distrib-max-right 0≤a =
        *-commute >=> *-distrib-max-left 0≤a >=> cong2 max *-commute *-commute

  module _ {{Min : MinOperationStr LO}} where
    abstract
      *-distrib-min-left : {a b c : D} -> 0# ≤ a -> a * min b c == min (a * b) (a * c)
      *-distrib-min-left {a} {b} {c} 0≤a = antisym-≤ abc≤abac (convert-≮ abc≮abac)
        where
        bc≤b : min b c ≤ b
        bc≤b = min-≤-left
        bc≤c : min b c ≤ c
        bc≤c = min-≤-right
        abc≤ab : (a * min b c) ≤ (a * b)
        abc≤ab = *₁-preserves-≤ 0≤a bc≤b
        abc≤ac : (a * min b c) ≤ (a * c)
        abc≤ac = *₁-preserves-≤ 0≤a bc≤c
        abc≤abac : (a * min b c) ≤ (min (a * b) (a * c))
        abc≤abac = min-greatest-≤ abc≤ab abc≤ac
        abc≮abac : (a * min b c) ≮ (min (a * b) (a * c))
        abc≮abac abc<abac = irrefl-< (min-greatest-< bc<b bc<c)
          where
          abc<ab : (a * (min b c)) < (a * b)
          abc<ab = trans-<-≤ abc<abac min-≤-left
          abc<ac : (a * (min b c)) < (a * c)
          abc<ac = trans-<-≤ abc<abac min-≤-right
          a≮0 : a ≮ 0#
          a≮0 = convert-≤ 0≤a
          bc<b : min b c < b
          bc<b = *₁-reflects-< a≮0 abc<ab
          bc<c : min b c < c
          bc<c = *₁-reflects-< a≮0 abc<ac

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

      *-distrib-flip-min-left : {a b c : D} -> a ≤ 0# -> a * min b c == max (a * b) (a * c)
      *-distrib-flip-min-left {a} {b} {c} a≤0 = antisym-≤ (convert-≮ abac≮abc) abac≤abc
        where
        bc≤b : min b c ≤ b
        bc≤b = min-≤-left
        bc≤c : min b c ≤ c
        bc≤c = min-≤-right
        ab≤abc : (a * b) ≤ (a * min b c)
        ab≤abc = *₁-flips-≤ a≤0 bc≤b
        ac≤abc : (a * c) ≤ (a * min b c)
        ac≤abc = *₁-flips-≤ a≤0 bc≤c
        abac≤abc : max (a * b) (a * c) ≤ (a * min b c)
        abac≤abc = max-least-≤ ab≤abc ac≤abc
        abac≮abc : max (a * b) (a * c) ≮ (a * min b c)
        abac≮abc abac<abc = irrefl-< (min-greatest-< bc<b bc<c)
          where
          ab<abc : (a * b) < (a * (min b c))
          ab<abc = trans-≤-< max-≤-left abac<abc
          ac<abc : (a * c) < (a * (min b c))
          ac<abc = trans-≤-< max-≤-right abac<abc
          0≮a : 0# ≮ a
          0≮a = convert-≤ a≤0
          bc<b : min b c < b
          bc<b = *₁-flip-reflects-< 0≮a ab<abc
          bc<c : min b c < c
          bc<c = *₁-flip-reflects-< 0≮a ac<abc
