{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.triangular-numbers.factorial-path where

open import additive-group
open import additive-group.instances.nat
open import base
open import combinatorics.binomial-coefficients
open import combinatorics.descending-factorial
open import combinatorics.triangular-numbers
open import equality-path
open import semiring
open import semiring.instances.nat

private
  triangular-number-rational-path' : ∀ n -> triangular-number n * 2 == falling-factorial (suc n) 2
  triangular-number-rational-path' zero = refl
  triangular-number-rational-path' (suc n) =
    cong (binomial-coeff' n 2 *_) (*-right-one) >=> sym (falling-factorial-binom-coeff'-path 2 n)

triangular-number-2-path : ∀ n -> triangular-number n * 2 == (suc n) * n
triangular-number-2-path n =
  triangular-number-rational-path' n >=>
  cong (suc n *_) (falling-factorial-one₂ n)
