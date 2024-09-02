{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.order where

open import additive-group.instances.real
open import base
open import fin
open import finset.instances
open import finsum.order
open import heyting-field.instances.real
open import nat
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.exponential-series
open import real.sequence.limit.order
open import sequence.partial-sums

private
  opaque
    exp-abs-≤ : {x : ℝ} -> exp x ≤ exp (abs x)
    exp-abs-≤ {x} = isLimit-preserves-≤ (isLimit-exp x) (isLimit-exp (abs x)) seq≤
      where
      term≤ : (i : ℕ) -> (exp-terms x i) ≤ (exp-terms (abs x) i)
      term≤ i = *₁-preserves-≤ (weaken-< (0<1/ℕ _)) (^ℕ-abs-≤ i)

      seq≤ : (i : ℕ) -> partial-sums (exp-terms x) i ≤ partial-sums (exp-terms (abs x)) i
      seq≤ i = finiteSum-preserves-≤ (\(i , _) -> term≤ i)

module _ (magic : Magic) where

  -- Goals
  exp-preserves-< : {x y : ℝ} -> x < y -> exp x < exp y
  exp-preserves-< = magic

  exp-reflects-< : {x y : ℝ} -> exp x < exp y -> x < y
  exp-reflects-< = magic

  exp-preserves-≤ : {x y : ℝ} -> x ≤ y -> exp x ≤ exp y
  exp-preserves-≤ = magic

  exp-reflects-≤ : {x y : ℝ} -> exp x ≤ exp y -> x ≤ y
  exp-reflects-≤ ex≤ey y<x = ex≤ey (exp-preserves-< y<x)
