{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.rational where

open import base
open import rational
open import ring
open import ring.implementations
open import semiring

instance
  RationalSemiring : Semiring Rational
  RationalSemiring = record
    { 0# = 0r
    ; 1# = 1r
    ; _+_ = _r+_
    ; _*_ = _r*_
    ; +-assoc = (\ {m} {n} {o} -> (r+-assoc m n o))
    ; +-commute = (\ {m} {n} -> (r+-commute m n))
    ; *-assoc = (\ {m} {n} {o} -> (r*-assoc m n o))
    ; *-commute = (\ {m} {n} -> (r*-commute m n))
    ; +-left-zero = (\ {n} -> r+-left-zero n)
    ; *-left-zero = (\ {n} -> r*-left-zero n)
    ; *-left-one = (\ {n} -> r*-left-one n)
    ; *-distrib-+-right = (\ {m} {n} {o} -> r*-distrib-r+-right m n o)
    ; isSetDomain = isSetRational
    }
module RationalSemiring = Semiring RationalSemiring

instance
  RationalRing : Ring RationalSemiring
  RationalRing = record
    { -_ = r-_
    ; +-inverse = (\ {a} -> r+-inverse a)
    }
module RationalRing = Ring RationalRing


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
