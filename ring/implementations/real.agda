{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.real where

open import base
open import equality-path
open import nat
open import rational
open import real
open import real.arithmetic.rational
open import real.rational
open import ring.implementations.rational
open import semiring
open import semiring.initial
open import semiring.natural-reciprocal

open import ring.implementations.real.base public

instance
  ℕ->Semiring-ℝ : ℕ->Semiring-Op ℝ
  ℕ->Semiring-ℝ = ℕ->SemiringStr-cons Semiringʰ-ℕ->ℝ

private
  opaque
    ℕ-1/ℕ-path-ℝ : (n : Nat⁺) -> (ℚ->ℝ (ℕ->ℚ ⟨ n ⟩)) * (ℚ->ℝ (1/ℕ n)) == 1#
    ℕ-1/ℕ-path-ℝ n =
      sym (Semiringʰ.preserves-* Semiringʰ-ℚ->ℝ _ _) >=>
      cong ℚ->ℝ (ℕ-1/ℕ-path n)

instance
  1/ℕ-Op-ℝ : 1/ℕ-Op ℝ
  1/ℕ-Op-ℝ = record
    { f = \n -> ℚ->ℝ (1/ℕ n)
    ; path = ℕ-1/ℕ-path-ℝ
    }
