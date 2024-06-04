{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.non-trivial.instances.rational where

open import order
open import ordered-semiring.non-trivial
open import rational
open import rational.order
open import semiring

instance
  NonTrivalLinearlyOrderedSemiringStr-ℚ :
    NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℚ
  NonTrivalLinearlyOrderedSemiringStr-ℚ = record { 0<1 = Pos-0< 1# Pos-1r }
