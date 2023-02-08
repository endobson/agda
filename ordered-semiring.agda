{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring where

open import additive-group
open import base
open import equality
open import order
open import semiring
open import sum
open import truncation

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
      *₁-flips-< : {a b c : D} -> a < 0# -> b < c -> (a * c) < (a * b)

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

    *₁-flips-< : {a b c : D} -> (a < 0#) -> (b < c) -> (a * c) < (a * b)
    *₁-flips-< = LOS.*₁-flips-<

    *₂-flips-< : {a b c : D} -> (a < b) -> (c < 0#) -> (b * c) < (a * c)
    *₂-flips-< a<b c<0 =
      subst2 _<_ *-commute *-commute (*₁-flips-< c<0 a<b)

    *-flips-<0 : {a b : D} -> a < 0# -> b < 0# -> 0# < (a * b)
    *-flips-<0 {a} {b} a<0 b<0 = subst (_< (a * b)) *-left-zero (*₂-flips-< a<0 b<0)



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : LinearOrderStr D ℓ<) where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  record StronglyLinearlyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
    no-eta-equality
    field
      +₁-reflects-< : {a b c : D} -> (a + b) < (a + c) -> b < c
      *₁-fully-reflects-< : {a b c : D} -> (a * b) < (a * c) ->
        (b < c × 0# < a) ⊎ (c < b × a < 0#)

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S O}} where
  private
    module SLOS = StronglyLinearlyOrderedSemiringStr SLOS
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    +₁-reflects-< : {a b c : D} -> (a + b) < (a + c) -> b < c
    +₁-reflects-< = SLOS.+₁-reflects-<

    +₂-reflects-< : {a b c : D} -> (a + c) < (b + c) -> a < b
    +₂-reflects-< ac<bc = +₁-reflects-< (subst2 _<_ +-commute +-commute ac<bc)

    +-reflects-< : {a b c d : D} -> (a + b) < (c + d) -> ∥ (a < c) ⊎ (b < d) ∥
    +-reflects-< {a} {b} {c} {d} ab<cd = ∥-map handle (comparison-< _ (c + b) _ ab<cd)
      where
      handle : ((a + b) < (c + b)) ⊎ ((c + b) < (c + d)) -> (a < c) ⊎ (b < d)
      handle = ⊎-map +₂-reflects-< +₁-reflects-<

    +-reflects-0< : {a b : D} -> 0# < (a + b) -> ∥ (0# < a) ⊎ (0# < b) ∥
    +-reflects-0< {a} {b} 0<ab = +-reflects-< (subst (_< (a + b)) (sym +-right-zero) 0<ab)

    *₁-fully-reflects-< : {a b c : D} -> (a * b) < (a * c) ->
                          (b < c × 0# < a) ⊎ (c < b × a < 0#)
    *₁-fully-reflects-< = SLOS.*₁-fully-reflects-<

    *₁-reflects-< : {a b c : D} -> (a ≮ 0#) -> (a * b) < (a * c) -> (b < c)
    *₁-reflects-< a≮0 ab<ac =
      proj₁ (proj-¬r (*₁-fully-reflects-< ab<ac) (\ (c<b , a<0) -> a≮0 a<0))

    *₂-reflects-< : {a b c : D} -> (a * c) < (b * c) -> (c ≮ 0#) -> (a < b)
    *₂-reflects-< {a} {b} {c} ac<bc c≮0 =
      *₁-reflects-< c≮0 (subst2 _<_ *-commute *-commute ac<bc)

    *₁-reflects-0< : {a b : D} -> (a ≮ 0#) -> 0# < (a * b) -> (0# < b)
    *₁-reflects-0< {a} {b} a≮0 0<ab =
      *₁-reflects-< a≮0 (subst (_< (a * b)) (sym *-right-zero) 0<ab)

    *₂-reflects-0< : {a b : D} -> 0# < (a * b) -> (b ≮ 0#) -> (0# < a)
    *₂-reflects-0< {a} {b} 0<ab b≮0 =
      *₂-reflects-< (subst (_< (a * b)) (sym *-left-zero) 0<ab) b≮0


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



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         (S : Semiring ACM) (LO : LinearOrderStr D ℓ<) (PO : PartialOrderStr D ℓ≤) where
  private
    instance
      IACM = ACM
      IS = S
      ILO = LO
      IPO = PO

  record StronglyPartiallyOrderedSemiringStr : Type (ℓ-max* 3 ℓ< ℓ≤ ℓD) where
    no-eta-equality
    field
      +₁-reflects-≤ : {a b c : D} -> (a + b) ≤ (a + c) -> b ≤ c
      *₁-reflects-≤ : {a b c : D} -> 0# < a -> (a * b) ≤ (a * c) -> b ≤ c
      *₁-flip-reflects-≤ : {a b c : D} -> a < 0# -> (a * b) ≤ (a * c) -> c ≤ b

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : LinearOrderStr D ℓ<} {PO : PartialOrderStr D ℓ≤}
         {{SPOS : StronglyPartiallyOrderedSemiringStr S LO PO}} where

  private
    module SPOS = StronglyPartiallyOrderedSemiringStr SPOS
    instance
      IACM = ACM
      IS = S
      IPO = PO
      ILO = LO

  abstract
    +₁-reflects-≤ : {a b c : D} -> (a + b) ≤ (a + c) -> b ≤ c
    +₁-reflects-≤ = SPOS.+₁-reflects-≤

    +₂-reflects-≤ : {a b c : D} -> (a + c) ≤ (b + c) -> a ≤ b
    +₂-reflects-≤ ac≤bc = +₁-reflects-≤ (subst2 _≤_ +-commute +-commute ac≤bc)

    *₁-reflects-≤ : {a b c : D} -> (0# < a) -> (a * b) ≤ (a * c) -> (b ≤ c)
    *₁-reflects-≤ = SPOS.*₁-reflects-≤

    *₂-reflects-≤ : {a b c : D} -> (a * c) ≤ (b * c) -> (0# < c) -> (a ≤ b)
    *₂-reflects-≤ {a} {b} {c} ac≤bc 0<c =
      *₁-reflects-≤ 0<c (subst2 _≤_ *-commute *-commute ac≤bc)
