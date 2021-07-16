{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring where

open import base
open import equality
open import order
open import ordered-semiring
open import semiring
open import ring

private
  variable
    ℓD ℓ< : Level

record LinearlyOrderedRingStr {D : Type ℓD} {S : Semiring D} (R : Ring S) (O : LinearOrderStr D ℓ<)
  : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
  field
    ordered-semiring : LinearlyOrderedSemiringStr S O


module _ {D : Type ℓD} {S : Semiring D} {R : Ring S} {O : LinearOrderStr D ℓ<}
         {{LOR : LinearlyOrderedRingStr R O}} where
  private
    instance
      ILOS = LinearlyOrderedRingStr.ordered-semiring LOR
      IS = Ring.semiring R
      IO = O
  open Ring R using (-_ ; +-inverse)

  abstract
    minus-flips-< : (a b : D) -> (a < b) -> (- b) < (- a)
    minus-flips-< a b a<b =
      subst2 _<_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-< ((- b) + (- a)) a b a<b)
