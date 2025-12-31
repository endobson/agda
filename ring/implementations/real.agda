{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.real where

open import real
open import real.arithmetic.rational
open import semiring.initial

open import ring.implementations.real.base public

instance
  ℕ->Semiring-ℝ : ℕ->Semiring-Op ℝ
  ℕ->Semiring-ℝ = ℕ->SemiringStr-cons Semiringʰ-ℕ->ℝ
