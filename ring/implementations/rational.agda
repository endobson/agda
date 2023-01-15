{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.rational where

open import base
open import additive-group.instances.nat
open import additive-group.instances.int
open import rational
open import ring
open import ring.implementations
open import semiring.instances.nat

open rational public using
  ( RationalRing
  ; RationalSemiring
  ; AdditiveCommMonoid-Rational
  )

Semiringʰ-ℤ->ℚ : Semiringʰ ℤ->ℚ
Semiringʰ-ℤ->ℚ = record
  { preserves-1# = refl
  ; preserves-+ = ℤ->ℚ-preserves-+
  ; preserves-* = ℤ->ℚ-preserves-*
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
