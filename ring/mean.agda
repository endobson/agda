{-# OPTIONS --cubical --safe --exact-split #-}

module ring.mean where

open import additive-group
open import base
open import equality-path
open import ring
open import semiring
open import semiring.initial
open import semiring.mean
open import semiring.natural-reciprocal

module _ {ℓD : Level} {D : Type ℓD}
         {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}}
         {{AG : AdditiveGroup ACM}}
         {{_ : ℕ->Semiring-Op D}}
         {{_ : 1/ℕ-Op D}}
  where
  opaque
    mean-+-diff/2 : {x y : D} -> mean x y + (diff x y * 1/2) == y
    mean-+-diff/2 {x} {y} =
      sym *-distrib-+-right >=>
      cong (_* 1/2)
        (+-left +-commute >=>
         +-assoc >=>
         +-right diff-step) >=>
      *-distrib-+-right >=>
      +-/2-path

    mean-minus-diff/2 : {x y : D} -> mean x y + (- (diff x y * 1/2)) == x
    mean-minus-diff/2 =
      +-cong mean-commute (sym minus-extract-left >=> *-left (sym diff-anticommute)) >=>
      mean-+-diff/2

    diff-mean : {x y : D} -> diff (mean x y) y == diff x y * 1/2
    diff-mean = +-left (sym mean-+-diff/2) >=> +-assoc >=> diff-step

    diff-mean' : {x y : D} -> diff x (mean x y) == diff x y * 1/2
    diff-mean' = +-right (cong -_ (sym mean-minus-diff/2) >=> sym diff-anticommute) >=> diff-step
