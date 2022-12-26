{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.indicator where

open import additive-group
open import nat
open import base
open import ring
open import semiring


module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

  Ind : Nat⁺ -> D
  Ind (suc zero , _) = 1#
  Ind (suc (suc _) , _) = 0#
