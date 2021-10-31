{-# OPTIONS --cubical --safe --exact-split #-}

module real.linear-combo where

open import additive-group
open import additive-group.instances.real
open import base
open import real
open import ring.implementations.real
open import ring
open import semiring


LinearCombo' : ℝ -> ℝ -> ℝ -> Type₁
LinearCombo' a b c = Σ[ k ∈ ℝ ] ((k * a) + ((1# + (- k)) * b) == c)
