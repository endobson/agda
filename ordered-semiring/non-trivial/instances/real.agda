{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.non-trivial.instances.real where

open import additive-group
open import order
open import order.instances.real
open import ordered-semiring.instances.real
open import ordered-semiring.non-trivial
open import ordered-semiring.non-trivial.instances.rational
open import real.rational
open import ring.implementations.rational
open import semiring

instance
  NonTrivalLinearlyOrderedSemiringStr-ℝ :
    NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℝ
  NonTrivalLinearlyOrderedSemiringStr-ℝ = record { 0<1 = ℚ->ℝ-preserves-< 0<1 }
