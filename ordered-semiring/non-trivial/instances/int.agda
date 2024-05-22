{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.non-trivial.instances.int where

open import additive-group
open import additive-group.instances.int
open import base
open import order
open import order.instances.int
open import ordered-semiring.instances.int
open import ordered-semiring.non-trivial

instance
  NonTrivalLinearlyOrderedSemiringStr-ℤ :
    NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℤ
  NonTrivalLinearlyOrderedSemiringStr-ℤ = record { 0<1 = ( 1 , tt) , +-right-zero }

  NonTrivalPartiallyOrderedSemiringStr-ℤ :
    NonTrivialPartiallyOrderedSemiringStr PartiallyOrderedSemiringStr-ℤ
  NonTrivalPartiallyOrderedSemiringStr-ℤ = record { 0≤1 = weaken-< 0<1 }
