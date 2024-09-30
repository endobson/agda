{-# OPTIONS --cubical --safe --exact-split #-}

module real.irrational where

open import apartness
open import base
open import order.instances.real
open import rational
open import real
open import real.rational
open import relation

isIrrational : Pred ℝ ℓ-one
isIrrational x = ∀ (q : ℚ) -> x # (ℚ->ℝ q)
