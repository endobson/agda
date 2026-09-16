{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.absolute-convergence where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.partition
open import finset
open import finset.detachable
open import finset.instances
open import finsum
open import finsum.absolute-value
open import finsum.indicator
open import finsum.order
open import functions
open import funext
open import hlevel
open import isomorphism
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import rational
open import real
open import real.epsilon-bounded
open import real.order
open import real.sequence.limit
open import metric-space.cauchy
open import metric-space.instances.real
open import real.subspace
open import real.sequence.cauchy
open import real.series.base
open import real.series
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import sequence
open import sequence.partial-sums
open import sequence.permutation
open import sigma
open import sigma.base
open import subset
open import subset.indicator
open import truncation
open import type-algebra


-- isAbsConvergentSeries-≤ :
--   {s₁ s₂ : Sequence ℝ} ->
--   (∀ i -> abs (s₁ i) ≤ abs (s₂ i)) ->
--   isAbsConvergentSeries s₂ ->
--   isAbsConvergentSeries s₁
-- isAbsConvergentSeries-≤ {s₁} {s₂} lt ac₂ = ac₁
--   where
--
--   cauchy-a₂ : isCauchy (partial-sums (abs ∘ s₂))
--   cauchy-a₂ = isConvergentSequence->isCauchy ac₂
--
--
--   cauchy-a₁ : isCauchy (partial-sums (abs ∘ s₁))
--   cauchy-a₁ = ?
--
--   ac₁ : isAbsConvergentSeries s₁
--   ac₁ = isCauchy->isConvergentSequence cauchy-a₁
