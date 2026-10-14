{-# OPTIONS --cubical --safe --exact-split #-}

module real.power-series.eval where

open import power-series
open import real
open import real.sequence.limit
open import sequence.partial-sums
open import base
open import metric-space.uniformly-continuous
open import metric-space.instances.real
open import nat
open import additive-group.instances.real
open import sequence
open import semiring
open import ring.implementations.real
open import semiring.exponentiation
open import subset
open import subset.subspace

power-series->partial-sums : (p : PowerSeries ℝ) (x : ℝ) -> Sequence ℝ
power-series->partial-sums (power-series c) x =
  partial-sums (\i -> (c i) * (x ^ℕ i))

power-series-approximation : (p : PowerSeries ℝ) (i : ℕ) -> (x : ℝ) -> ℝ
power-series-approximation p i x = power-series->partial-sums p x i


module _ {ℓS : Level} (p : PowerSeries ℝ) (S : Subtype ℝ ℓS) (f : Subspace S -> ℝ) where
  record isRestrictedPowerSeriesEval : Type (ℓ-max ℓ-one ℓS) where
    field
      limit : ∀ (x∈@(x , _) : Subspace S) -> isLimit (power-series->partial-sums p x) (f x∈)


isPowerSeriesEval : (p : PowerSeries ℝ) (f : ℝ -> ℝ) -> Type ℓ-one
isPowerSeriesEval p f = isRestrictedPowerSeriesEval p (UnivS ℝ) (restrict f _)

module _ (magic : Magic) where
  isLocallyUniformlyContinuous-power-series-approximation :
    (p : PowerSeries ℝ) (i : ℕ) -> isLocallyUniformlyContinuous (power-series-approximation p i)
  isLocallyUniformlyContinuous-power-series-approximation = magic
