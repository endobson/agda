{-# OPTIONS --cubical --safe --exact-split #-}

module ring.division where

open import additive-group
open import base
open import equality-path
open import hlevel
open import semiring
open import ring
open import semiring.division
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}}
         {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

  private
    div'-negate : {d n : D} -> d div' n -> d div' (- n)
    div'-negate (a , pr) =
      (- a) , (minus-extract-left >=> (cong -_ pr))

  div-negate : {d n : D} -> d div n -> d div (- n)
  div-negate = ∥-map div'-negate

  private
    div'-negate-left : {d n : D} -> d div' n -> (- d) div' n
    div'-negate-left (a , pr) = (- a) , (minus-extract-both >=> pr)

  div-negate-left : {d n : D} -> d div n -> (- d) div n
  div-negate-left = ∥-map div'-negate-left
