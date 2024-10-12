{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.int where

open import additive-group
open import additive-group.instances.int
open import base
open import equality
open import nat.arithmetic
open import order
open import order.instances.int
open import ordered-additive-group.instances.int
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.ring
open import ring.implementations.int
open import semiring

import int.order as io

abstract
  instance
    LinearlyOrderedSemiringStr-ℤ : LinearlyOrderedSemiringStr IntSemiring useⁱ
    LinearlyOrderedSemiringStr-ℤ = LinearlyOrderedSemiringStr-Ring
      (\ 0<a b<c -> io.*₁-Pos-preserves-<⁺ b<c (io.>0->Pos 0<a))

    NonTrivalLinearlyOrderedSemiringStr-ℤ :
      NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℤ
    NonTrivalLinearlyOrderedSemiringStr-ℤ = record { 0<1 = ( 1 , tt) , +-right-zero }

    PartiallyOrderedSemiringStr-ℤ : PartiallyOrderedSemiringStr IntSemiring useⁱ
    PartiallyOrderedSemiringStr-ℤ = PartiallyOrderedSemiringStr-Ring
      (weaken-< 0<1)
      (\ 0≤a b≤c -> io.*₁-NonNeg-preserves-≤⁺ b≤c (io.≥0->NonNeg 0≤a))
