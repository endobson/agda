{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.real where

open import additive-group.instances.real
open import base
open import order.instances.real
open import ordered-additive-group.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.negated
open import ordered-semiring.ring
open import real.arithmetic.order
open import real.rational
open import ring.implementations.real

instance
  LinearlyOrderedSemiringStr-ℝ : LinearlyOrderedSemiringStr ℝSemiring useⁱ
  LinearlyOrderedSemiringStr-ℝ = LinearlyOrderedSemiringStr-Ring
    (ℝ*₁-preserves-< _ _ _)

  PartiallyOrderedSemiringStr-ℝ : PartiallyOrderedSemiringStr ℝSemiring useⁱ
  PartiallyOrderedSemiringStr-ℝ = PartiallyOrderedSemiringStr-Negated _ _

  NonTrivalLinearlyOrderedSemiringStr-ℝ :
    NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℝ
  NonTrivalLinearlyOrderedSemiringStr-ℝ = record { 0<1 = ℚ->ℝ-preserves-< 0<1 }
