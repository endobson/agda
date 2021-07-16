{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring where

open import base
open import equality
open import order
open import semiring

private
  variable
    ℓD ℓ< : Level

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
