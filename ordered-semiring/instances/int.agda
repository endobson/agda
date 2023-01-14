{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.int where

open import base
open import equality
open import nat.arithmetic
open import order
open import order.instances.int
open import ordered-semiring
open import ring.implementations
open import semiring

import int.order as io

abstract
  instance
    LinearlyOrderedSemiringStr-ℕ : LinearlyOrderedSemiringStr IntSemiring useⁱ
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.+₁-preserves-< =
      io.+₁-preserves-< _
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.*₁-preserves-< 0<a b<c =
      io.*₁-Pos-preserves-<⁺ b<c (io.>0->Pos 0<a)

    PartiallyOrderedSemiringStr-ℕ : PartiallyOrderedSemiringStr IntSemiring useⁱ
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.+₁-preserves-≤ =
      io.+₁-preserves-≤ _
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.*₁-preserves-≤ 0≤a b≤c =
      io.*₁-NonNeg-preserves-≤⁺ b≤c (io.≥0->NonNeg 0≤a)
