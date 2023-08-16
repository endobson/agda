{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring where

open import additive-group
open import base
open import equality
open import hlevel
open import order
open import ordered-additive-group
open import ordered-semiring
open import relation
open import ring
open import semiring
open import sum
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {{AG : AdditiveGroup ACM}}
         {O : isPartialOrder D≤}
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
