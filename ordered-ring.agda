{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring where

open import additive-group
open import base
open import equality
open import hlevel
open import order
open import ordered-additive-group
open import ordered-semiring
open import ring
open import semiring
open import sum
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {{AG : AdditiveGroup ACM}}
         {O : LinearOrderStr D ℓ<}
         {{LOA : LinearlyOrderedAdditiveStr ACM O}}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    1≮0 : 1# ≮ 0#
    1≮0 1<0 = irrefl-< (trans-< -1<0 0<-1)
      where
      module _ where
        0<-1 = minus-flips-<0 1<0
        -1<0 = subst2 _<_ *-left-one *-left-one (*₁-flips-< 1<0 0<-1)


module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {{AG : AdditiveGroup ACM}}
         {O : PartialOrderStr D ℓ<}
         {{POA : PartiallyOrderedAdditiveStr ACM O}}
         {{POS : PartiallyOrderedSemiringStr S O}}
         where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    *₁-flips-≤ : {a b c : D} -> (a ≤ 0#) -> (b ≤ c) -> (a * c) ≤ (a * b)
    *₁-flips-≤ {a} {b} {c} a≤0 b≤c =
      subst2 _≤_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-≤ (*₁-preserves-≤ 0≤-a b≤c))
      where
      module _ where
        0≤-a : 0# ≤ (- a)
        0≤-a = (minus-flips-≤0 a≤0)

    *₂-flips-≤ : {a b c : D} -> (a ≤ b) -> (c ≤ 0#) -> (b * c) ≤ (a * c)
    *₂-flips-≤ {a} {b} {c} a≤b c≤0 =
      subst2 _≤_ *-commute *-commute (*₁-flips-≤ c≤0 a≤b)


module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {{AG : AdditiveGroup ACM}}
         {O : PartialOrderStr D ℓ≤}
         {{TO : TotalOrderStr O}}
         {{POA : PartiallyOrderedAdditiveStr ACM O}}
         {{POS : PartiallyOrderedSemiringStr S O}}
         where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  abstract
    0≤-square : {a : D} -> 0# ≤ (a * a)
    0≤-square {a} = unsquash isProp-≤ (∥-map handle (connex-≤ 0# a))
      where
      handle : (0# ≤ a) ⊎ (a ≤ 0#) -> 0# ≤ (a * a)
      handle (inj-l 0≤a) = subst2 _≤_ *-right-zero refl (*₁-preserves-≤ 0≤a 0≤a)
      handle (inj-r a≤0) = subst2 _≤_ *-right-zero refl (*₁-flips-≤ a≤0 a≤0)
