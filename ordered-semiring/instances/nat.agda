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
      transport (no.+-left-< _)
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.*₁-preserves-< {a} {b} {c} 0<a b<c =
      (no.*-left-<⁺ 0<a b<c)

    PartiallyOrderedSemiringStr-ℕ : PartiallyOrderedSemiringStr NatSemiring PartialOrderStr-ℕ
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.+₁-preserves-≤ =
      transport (no.+-left-≤ _)
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.*₁-preserves-≤ {a} {b} 0≤a 0≤b =
      (no.*-left-≤⁺ a 0≤b)
