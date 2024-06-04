{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.rational where

open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import rational
open import ring
open import ring.implementations.int
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import truncation

open rational public using
  ( Ring-ℚ
  ; Semiring-ℚ
  ; AdditiveCommMonoid-ℚ
  )

Semiringʰ-ℤ->ℚ : Semiringʰ ℤ->ℚ
Semiringʰ-ℤ->ℚ = record
  { +ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = ℤ->ℚ-preserves-+
    }
  ; *ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = ℤ->ℚ-preserves-*
    }
  }

Ringʰ-ℤ->ℚ : Ringʰ ℤ->ℚ
Ringʰ-ℤ->ℚ = record
  { preserves-0# = refl
  ; preserves-1# = refl
  ; preserves-+ = ℤ->ℚ-preserves-+
  ; preserves-* = ℤ->ℚ-preserves-*
  ; preserves-minus = ℤ->ℚ-preserves-minus
  }

Semiringʰ-ℕ->ℚ : Semiringʰ ℕ->ℚ
Semiringʰ-ℕ->ℚ = Semiringʰ-∘ Semiringʰ-ℤ->ℚ Semiringʰ-ℕ->ℤ
module Semiringʰ-ℕ->ℚ = Semiringʰ Semiringʰ-ℕ->ℚ

abstract
  ℕ->Semiring-ℚ-path : ∀ n -> ℕ->Semiring n == ℕ->ℚ n
  ℕ->Semiring-ℚ-path n = (\i -> ∃!-unique ∃!ℕ->Semiring ℕ->ℚ Semiringʰ-ℕ->ℚ i n)
