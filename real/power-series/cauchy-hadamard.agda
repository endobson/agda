{-# OPTIONS --cubical --safe --exact-split #-}

module real.power-series.cauchy-hadamard where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import fin
open import fin.sum-pair
open import finset.instances
open import finset.instances.sum-pair
open import finsum
open import finsum.absolute-value
open import finsum.arithmetic
open import finsum.order
open import functions
open import funext
open import heyting-field.instances.real
open import inhabited.instances.nat
open import metric-space
open import metric-space.uniformly-continuous
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import nat
open import order
open import power-series
open import order.bound
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.big-o
open import ordered-semiring.big-o.arithmetic
open import ordered-semiring.big-o.common
open import ordered-semiring.instances.real
open import ordered-semiring.mean
open import real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.nth-root
open import real.distance
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.minmax
open import real.sequence.limit.order
open import real.series
open import real.power-series.eval
open import real.series.big-o
open import real.series.cauchy-product
open import real.series.geometric
open import real.subspace
open import ring
open import ring.exponentiation.diff
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import semiring.mean
open import sequence
open import sequence.partial-sums
open import subset
open import subset.subspace
open import truncation


private
  abs⁰⁺ : ℝ -> ℝ⁰⁺
  abs⁰⁺ x = abs x , abs-0≤


module _
  (magic : Magic)
  (p@(power-series c) : PowerSeries ℝ)
  {lim⁺@(lim , 0<lim) : ℝ⁺}
  (bounded : ∀Largeℕ (\i -> nthRoot (suc i , tt) (abs⁰⁺ (c (suc i))) < lim))
  -- (lim-sup : isLimitSuperior (\i -> nthRoot (suc i) (abs⁰⁺ (c (suc i)))) 0#)
  where
  private
    S : Subtype ℝ ℓ-one
    S x = abs x < ℝ1/ (lim , inj-r 0<lim) , isProp-<

  restricted-eval-power-series/cauchy-hadamard :
    Σ (Subspace S -> ℝ) (isRestrictedPowerSeriesEval p S)
  restricted-eval-power-series/cauchy-hadamard = magic

  -- isLimit-eval-cauchy-hadamard-power-series :
  --   ∀ (x : ℝ) -> isLimit (partial-sums (\i -> c i × x ^ℕ i))
  --                        (eval-cauchy-hadam
