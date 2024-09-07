{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.order.increasing where

open import order
open import order.instances.real
open import real
open import real.exponential-series

open import real.exponential.order.increasing.preserves public
open import real.exponential.order.increasing.reflects public

exp-reflects-≤ : {x y : ℝ} -> exp x ≤ exp y -> x ≤ y
exp-reflects-≤ ex≤ey y<x = ex≤ey (exp-preserves-< y<x)

exp-preserves-≤ : {x y : ℝ} -> x ≤ y -> exp x ≤ exp y
exp-preserves-≤ x≤y ey<ex = x≤y (exp-reflects-< ey<ex)
