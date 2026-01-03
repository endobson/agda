{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.rational where

open import base
open import ordered-semiring
open import ordered-semiring.decidable
open import rational
open import rational.order
open import semiring

open import rational.order public using
  ( LinearlyOrderedSemiringStr-ℚ
  ; PartiallyOrderedSemiringStr-ℚ
  ; StronglyLinearlyOrderedSemiringStr-ℚ
  )

instance
  NonTrivalLinearlyOrderedSemiringStr-ℚ :
    NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℚ
  NonTrivalLinearlyOrderedSemiringStr-ℚ = record { 0<1 = Pos-0< 1# Pos-1r }

  StronglyPartiallyOrderedSemiringStr-ℚ :
    StronglyPartiallyOrderedSemiringStr Semiring-ℚ useⁱ useⁱ
  StronglyPartiallyOrderedSemiringStr-ℚ = StronglyPartiallyOrderedSemiringStr-Dec<
