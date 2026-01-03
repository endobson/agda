{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.mean where

open import additive-group
open import base
open import semiring
open import semiring.initial
open import semiring.natural-reciprocal


module _ {ℓD : Level} {D : Type ℓD}
         {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}}
         {{_ : ℕ->Semiring-Op D}}
         {{_ : 1/ℕ-Op D}}
         where
  private
    instance
      IACM = ACM

  mean : D -> D -> D
  mean x y = (x + y) * 1/2

  mean-commute : {x y : D} -> mean x y == mean y x
  mean-commute = *-left +-commute
