{-# OPTIONS --cubical --safe --exact-split #-}

module ring.arithmetic where

open import base
open import equality
open import ring
open import semiring


private
  variable
    ℓD : Level

module _ {D : Type ℓD} {{R : Ring D}} where
  private
    instance
      I-SR = Ring.semiring R
  open Ring R

  +-right-injective : (a b c : D) -> (a + c) == (b + c) -> a == b
  +-right-injective a b c p =
    sym (+-assoc >=> cong (a +_) +-inverse >=> +-right-zero) >=>
    cong (_+ (- c)) p >=>
    +-assoc >=> cong (b +_) +-inverse >=> +-right-zero
