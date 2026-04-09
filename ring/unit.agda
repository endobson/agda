{-# OPTIONS --cubical --safe --exact-split #-}

module ring.unit where

open import additive-group
open import base
open import equality-path
open import ring
open import semiring
open import semiring.unit

module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} {{AG : AdditiveGroup ACM}} where

  u--closed : {x : D} -> isUnit x -> isUnit (- x)
  u--closed {x} (is-unit inv p) = (is-unit (- inv) -p)
    where
    opaque
      -p : (- x * - inv) == 1#
      -p = minus-extract-both >=> p
