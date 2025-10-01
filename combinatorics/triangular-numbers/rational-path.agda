{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.triangular-numbers.rational-path where

open import additive-group.instances.nat
open import base
open import combinatorics.triangular-numbers
open import combinatorics.triangular-numbers.factorial-path
open import equality-path
open import int.base
open import int.nat
open import rational
open import ring.implementations.rational
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import semiring.natural-reciprocal

triangular-number-rational-path : ∀ n -> ℕ->ℚ (triangular-number n) == ℕ->ℚ ((suc n) * n) * 1/2
triangular-number-rational-path n =
  sym *-right-one >=>
  *-right (sym 2/2-path) >=>
  sym *-assoc >=>
  *-left (
    (*-right (sym ℕ->Semiring-preserves-2#) >=>
     sym (Semiringʰ.preserves-* ℕ->Semiringʰ _ _) >=>
     cong ℕ->ℚ (triangular-number-2-path n)))
