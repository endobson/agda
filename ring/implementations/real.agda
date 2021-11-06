{-# OPTIONS --cubical --safe --exact-split #-}

module ring.implementations.real where

open import additive-group.instances.real
open import real
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.associative
open import real.arithmetic.multiplication.distributive
open import real.rational
open import ring
open import ring.implementations
open import semiring


instance
  ℝSemiring : Semiring AdditiveCommMonoid-ℝ
  ℝSemiring = record
    { 1# = 1ℝ
    ; _*_ = _ℝ*_
    ; *-assoc = (\ {m} {n} {o} -> (ℝ*-assoc m n o))
    ; *-commute = (\ {m} {n} -> (ℝ*-commute m n))
    ; *-left-zero = (\ {n} -> ℝ*-left-zero n)
    ; *-left-one = (\ {n} -> ℝ*-left-one n)
    ; *-distrib-+-right = (\ {m} {n} {o} -> ℝ*-distrib-ℝ+-right m n o)
    ; isSet-Domain = isSet-ℝ
    }
module ℝSemiring = Semiring ℝSemiring


instance
  ℝRing : Ring ℝSemiring AdditiveGroup-ℝ
  ℝRing = record {}
module ℝRing = Ring ℝRing
