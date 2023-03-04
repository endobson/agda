{-# OPTIONS --cubical --safe --exact-split #-}

module ring.arithmetic where

open import additive-group
open import base
open import equality
open import ring
open import semiring


private
  variable
    ℓD : Level

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}}
         where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S

  +-right-injective : (a b c : D) -> (a + c) == (b + c) -> a == b
  +-right-injective a b c p =
    sym (+-assoc >=> cong (a +_) +-inverse >=> +-right-zero) >=>
    cong (_+ (- c)) p >=>
    +-assoc >=> cong (b +_) +-inverse >=> +-right-zero
