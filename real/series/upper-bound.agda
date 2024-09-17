{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.upper-bound where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import fin
open import finite-commutative-semigroup.minmax
open import finset.instances
open import functions
open import metric-space
open import metric-space.instances.real
open import order
open import order.bound
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.sequence.limit
open import real.series
open import ring.implementations.real
open import semiring
open import sequence
open import subset.subspace
open import truncation

opaque
  isConvergentSeries->UpperBound :
    {s : Sequence ℝ} -> (isConvergentSeries s) -> ∃ ℝ (isUpperBound (abs ∘ s))
  isConvergentSeries->UpperBound {s} conv =
    ∥-map handle (isLimit.distance<ε (isConvergentSeries->zero-limit conv) (1# , 0<1))
    where
    handle : ∀Largeℕ' (\i -> distance 0# (s i) < 1#) -> Σ ℝ (isUpperBound (abs ∘ s))
    handle (N , ds<1) = (max initMax 1#) , upper
      where
      as<1 : ∀ i -> N ≤ i -> abs (s i) < 1#
      as<1 i n≤i = trans-=-< (cong abs (sym diff0-path)) (ds<1 i n≤i)
      initMax : ℝ
      initMax = finite⁺Max (\((i , _) : Fin (suc N)) -> abs (s i))

      upper : isUpperBound (abs ∘ s) (max initMax 1#)
      upper i = handle2 (split-< i (suc N))
        where
        handle2 : (i < (suc N) ⊎ (suc N ≤ i)) -> abs (s i) ≤ (max initMax 1#)
        handle2 (inj-l i<sN) = trans-≤ (finite⁺Max-≤ (i , i<sN)) max-≤-left
        handle2 (inj-r sN≤i) = weaken-< (trans-<-≤ (as<1 i (weaken-< sN≤i)) max-≤-right)
