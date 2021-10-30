{-# OPTIONS --cubical --safe --exact-split #-}

module real.linear-combo where

open import base
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import ring.implementations.real


LinearCombo' : ℝ -> ℝ -> ℝ -> Type₁
LinearCombo' a b c = Σ[ k ∈ ℝ ] ((k ℝ* a) ℝ+ ((1ℝ ℝ+ (ℝ- k)) ℝ* b) == c)
