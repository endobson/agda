{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.real where

open import base
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.associative
open import real.arithmetic.multiplication.distributive
open import ring
open import ring.implementations
open import semiring


instance
  ℝSemiring : Semiring ℝ
  ℝSemiring = record
    { 0# = 0ℝ
    ; 1# = 1ℝ
    ; _+_ = _ℝ+_
    ; _*_ = _ℝ*_
    ; +-assoc = (\ {m} {n} {o} -> (ℝ+-assoc m n o))
    ; +-commute = (\ {m} {n} -> (ℝ+-commute m n))
    ; *-assoc = (\ {m} {n} {o} -> (ℝ*-assoc m n o))
    ; *-commute = (\ {m} {n} -> (ℝ*-commute m n))
    ; +-left-zero = (\ {n} -> ℝ+-left-zero n)
    ; *-left-zero = (\ {n} -> ℝ*-left-zero n)
    ; *-left-one = (\ {n} -> ℝ*-left-one n)
    ; *-distrib-+-right = (\ {m} {n} {o} -> ℝ*-distrib-ℝ+-right m n o)
    ; isSetDomain = isSet-ℝ
    }
module ℝSemiring = Semiring ℝSemiring


instance
  ℝRing : Ring ℝ
  ℝRing = record
    { semiring = ℝSemiring
    ; -_ = ℝ-_
    ; +-inverse = (\ {a} -> ℝ+-inverse a)
    }
module ℝRing = Ring ℝRing
