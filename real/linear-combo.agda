{-# OPTIONS --cubical --safe --exact-split #-}

module real.linear-combo where

open import base
open import equality
open import hlevel
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import sigma
open import ring.implementations.real
open import semiring


LinearCombo' : ℝ -> ℝ -> ℝ -> Type₁
LinearCombo' a b c = Σ[ k ∈ ℝ ] ((k ℝ* a) ℝ+ ((1ℝ ℝ+ (ℝ- k)) ℝ* b) == c)

-- isProp-LinearCombo' : (a b c : ℝ) (a#b : a ℝ# b) -> isProp (LinearCombo' a b c)
-- isProp-LinearCombo' a b c a#b (k1 , p1) (k2 , p2) = ΣProp-path (isSet-ℝ _ _) ?
--   where
--   p3 : (k1 ℝ* a) ℝ+ ((1ℝ ℝ+ (ℝ- k1)) ℝ* b) == (k2 ℝ* a) ℝ+ ((1ℝ ℝ+ (ℝ- k2)) ℝ* b)
--   p3 = p1 >=> sym p2
--
--   p4 : ((1ℝ ℝ+ (ℝ- k1)) ℝ* b) == b ℝ+ (k1 ℝ* (ℝ- b))
--   p4 = *-distrib-+-right >=> ?
