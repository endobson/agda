{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.nat where

open import base
open import equality
open import nat.arithmetic
open import order
open import order.instances.nat
open import ordered-semiring
open import ring.implementations
open import semiring

import nat.order as no

abstract
  instance
    LinearlyOrderedSemiringStr-ℕ : LinearlyOrderedSemiringStr NatSemiring LinearOrderStr-ℕ
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.+₁-preserves-< =
      no.+-left-<⁺ _
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.*₁-preserves-< =
      no.*-left-<⁺

    PartiallyOrderedSemiringStr-ℕ : PartiallyOrderedSemiringStr NatSemiring PartialOrderStr-ℕ
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.+₁-preserves-≤ =
      no.+-left-≤⁺ _
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.*₁-preserves-≤ {a} 0≤a =
      no.*-left-≤⁺ a
