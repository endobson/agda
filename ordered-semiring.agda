{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring where

open import additive-group using (AdditiveCommMonoid)
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
      IS = S
      IO = O

  record LinearlyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
    no-eta-equality
    field
      +₁-preserves-< : (a b c : D) -> b < c -> (a + b) < (a + c)
      *-preserves-0< : (a b : D) -> 0# < a -> 0# < b -> 0# < (a * b)

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S O}} where
  open LinearlyOrderedSemiringStr LOS public

  private
    instance
      IS = S
      IO = O
      ILOS = LOS

  abstract
    +₂-preserves-< : (a b c : D) -> a < b -> (a + c) < (b + c)
    +₂-preserves-< a b c a<b = subst2 _<_ +-commute +-commute (+₁-preserves-< c a b a<b)

    +-preserves-< : (a b c d : D) -> a < b -> c < d -> (a + c) < (b + d)
    +-preserves-< a b c d a<b c<d =
      trans-< (+₁-preserves-< a c d c<d) (+₂-preserves-< a b d a<b)

    +-preserves-0< : {a b : D} -> 0# < a -> 0# < b -> 0# < (a + b)
    +-preserves-0< {a} {b} 0<a 0<b =
      subst (_< (a + b)) +-right-zero (+-preserves-< 0# a 0# b 0<a 0<b)



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} (S : Semiring ACM) (O : PartialOrderStr D ℓ≤) where
  private
    instance
      IS = S
      IO = O

  record PartiallyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
    no-eta-equality
    field
      +₁-preserves-≤ : (a b c : D) -> b ≤ c -> (a + b) ≤ (a + c)
      *-preserves-0≤ : (a b : D) -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a * b)



module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM} {O : PartialOrderStr D ℓ<}
         {{POS : PartiallyOrderedSemiringStr S O}} where
  open PartiallyOrderedSemiringStr POS public

  private
    instance
      IS = S
      IO = O
      IPOS = POS

  abstract
    +₂-preserves-≤ : (a b c : D) -> a ≤ b -> (a + c) ≤ (b + c)
    +₂-preserves-≤ a b c a≤b = subst2 _≤_ +-commute +-commute (+₁-preserves-≤ c a b a≤b)

    +-preserves-≤ : (a b c d : D) -> a ≤ b -> c ≤ d -> (a + c) ≤ (b + d)
    +-preserves-≤ a b c d a≤b c≤d =
      trans-≤ (+₁-preserves-≤ a c d c≤d) (+₂-preserves-≤ a b d a≤b)
