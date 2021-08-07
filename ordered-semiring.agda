{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring where

open import base
open import equality
open import order
open import semiring

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} (S : Semiring D) (O : LinearOrderStr D ℓ<) where
  private
    instance
      IS = S
      IO = O

  record LinearlyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
    field
      +₁-preserves-< : (a b c : D) -> b < c -> (a + b) < (a + c)
      *-preserves-0< : (a b : D) -> 0# < a -> 0# < b -> 0# < (a * b)

module _ {D : Type ℓD} {S : Semiring D} {O : LinearOrderStr D ℓ<}
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


module _ {D : Type ℓD} (S : Semiring D) (O : TotalOrderStr D ℓ≤) where
  private
    instance
      IS = S
      IO = O

  record TotallyOrderedSemiringStr : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
    field
      +₁-preserves-≤ : (a b c : D) -> b ≤ c -> (a + b) ≤ (a + c)
      *-preserves-0≤ : (a b : D) -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a * b)



module _ {D : Type ℓD} {S : Semiring D} {O : TotalOrderStr D ℓ<}
         {{TOS : TotallyOrderedSemiringStr S O}} where
  open TotallyOrderedSemiringStr TOS public

  private
    instance
      IS = S
      IO = O
      ITOS = TOS

  abstract
    +₂-preserves-≤ : (a b c : D) -> a ≤ b -> (a + c) ≤ (b + c)
    +₂-preserves-≤ a b c a≤b = subst2 _≤_ +-commute +-commute (+₁-preserves-≤ c a b a≤b)

    +-preserves-≤ : (a b c d : D) -> a ≤ b -> c ≤ d -> (a + c) ≤ (b + d)
    +-preserves-≤ a b c d a≤b c≤d =
      trans-≤ (+₁-preserves-≤ a c d c≤d) (+₂-preserves-≤ a b d a≤b)
