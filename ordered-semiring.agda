{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring where

open import additive-group
open import base
open import equality
open import order
open import semiring

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : LinearOrderStr D ℓ<) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record LinearlyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
    no-eta-equality
    field
      +₁-preserves-< : {a b c : D} -> b < c -> (a + b) < (a + c)
      *₁-preserves-< : {a b c : D} -> 0# < a -> b < c -> (a * b) < (a * c)

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S O}} where

  private
    module LOS = LinearlyOrderedSemiringStr LOS
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    +₁-preserves-< : {a b c : D} -> b < c -> (a + b) < (a + c)
    +₁-preserves-< = LOS.+₁-preserves-<

    +₂-preserves-< : {a b c : D} -> a < b -> (a + c) < (b + c)
    +₂-preserves-< a<b = subst2 _<_ +-commute +-commute (+₁-preserves-< a<b)

    +-preserves-< : {a b c d : D} -> a < b -> c < d -> (a + c) < (b + d)
    +-preserves-< a<b c<d =
      trans-< (+₁-preserves-< c<d) (+₂-preserves-< a<b)

    +-preserves-0< : {a b : D} -> 0# < a -> 0# < b -> 0# < (a + b)
    +-preserves-0< {a} {b} 0<a 0<b =
      subst (_< (a + b)) +-right-zero (+-preserves-< 0<a 0<b)

    *₁-preserves-< : {a b c : D} -> 0# < a -> b < c -> (a * b) < (a * c)
    *₁-preserves-< = LOS.*₁-preserves-<

    *₂-preserves-< : {a b c : D} -> a < b -> 0# < c -> (a * c) < (b * c)
    *₂-preserves-< a<b 0<c =
      subst2 _<_ *-commute *-commute (*₁-preserves-< 0<c a<b)

    *-preserves-0< : {a b : D} -> 0# < a -> 0# < b -> 0# < (a * b)
    *-preserves-0< 0<a 0<b = trans-=-< (sym *-right-zero) (LOS.*₁-preserves-< 0<a 0<b)




module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : PartialOrderStr D ℓ≤) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record PartiallyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
    no-eta-equality
    field
      +₁-preserves-≤ : {a b c : D} -> b ≤ c -> (a + b) ≤ (a + c)
      *₁-preserves-≤ : {a b c : D} -> 0# ≤ a -> b ≤ c -> (a * b) ≤ (a * c)



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {O : PartialOrderStr D ℓ<}
         {{POS : PartiallyOrderedSemiringStr S O}} where

  private
    module POS = PartiallyOrderedSemiringStr POS
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    +₁-preserves-≤ : {a b c : D} -> b ≤ c -> (a + b) ≤ (a + c)
    +₁-preserves-≤ = POS.+₁-preserves-≤

    +₂-preserves-≤ : {a b c : D} -> a ≤ b -> (a + c) ≤ (b + c)
    +₂-preserves-≤ a≤b = subst2 _≤_ +-commute +-commute (+₁-preserves-≤ a≤b)

    +-preserves-≤ : {a b c d : D} -> a ≤ b -> c ≤ d -> (a + c) ≤ (b + d)
    +-preserves-≤ a≤b c≤d = trans-≤ (+₁-preserves-≤ c≤d) (+₂-preserves-≤ a≤b)

    +-preserves-0≤ : {a b : D} -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a + b)
    +-preserves-0≤ {a} {b} 0≤a 0≤b =
      subst (_≤ (a + b)) +-right-zero (+-preserves-≤ 0≤a 0≤b)

    *-preserves-0≤ : {a b : D} -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a * b)
    *-preserves-0≤ 0≤a 0≤b = trans-=-≤ (sym *-right-zero) (POS.*₁-preserves-≤ 0≤a 0≤b)

    *₁-preserves-≤ : {a b c : D} -> (0# ≤ a) -> (b ≤ c) -> (a * b) ≤ (a * c)
    *₁-preserves-≤ = POS.*₁-preserves-≤

    *₂-preserves-≤ : {a b c : D} -> (a ≤ b) -> (0# ≤ c) -> (a * c) ≤ (b * c)
    *₂-preserves-≤ {a} {b} {c} a≤b 0≤c =
      subst2 _≤_ *-commute *-commute (*₁-preserves-≤ 0≤c a≤b)
