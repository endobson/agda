{-# OPTIONS --cubical --safe --exact-split #-}

module real.infinite-sum.cauchy-triangle where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import combinatorics.triangle-numbers
open import cubical
open import decision
open import equality-path
open import equivalence
open import equivalence.base
open import fin.sum-pair
open import functions
open import funext
open import hlevel.base
open import hlevel.sigma
open import isomorphism
open import nat
open import nat.iteration
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import real
open import real.infinite-sum
open import real.infinite-sum.triangle
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import real.sequence.limit.order
open import real.sequence.limit.subsequence
open import real.series
open import real.series.base
open import real.series.cauchy-product
open import relation
open import ring.implementations.real
open import semiring
open import sequence
open import sequence.partial-sums
open import sequence.subsequence
open import sigma
open import sigma.base
open import truncation


module _
  {s₁ s₂ : Sequence ℝ}
  (ac₁ : isAbsConvergentSeries s₁)
  (ac₂ : isAbsConvergentSeries s₂)
  -- (lim₁ : isLimit (partial-sums s₁) v₁)
  -- (lim₂ : isLimit (partial-sums s₂) v₂)
  where

  private
    -- Diagonals
    s₃ : ℕ -> ℝ
    s₃ = cauchy-product s₁ s₂

    ac₃ : isAbsConvergentSeries s₃
    ac₃ = isAbsConvergentSeries-cauchy-product ac₁ ac₂
    -- lim₃ : isLimit (partial-sums s₃) (v₁ * v₂)
    -- lim₃ = isLimit-cauchy-product lim₁ lim₂ ac₁

    f : ℕ × ℕ -> ℝ
    f (i , j) = s₁ i * s₂ j

    s₄ : ℕ -> ℝ
    s₄ = f ∘ (isEqInv isEquiv-triangle-encode)

  isSubsequenceOf-s₄s₃ : isSubsequenceOf (partial-sums s₄) (partial-sums s₃)
  isSubsequenceOf-s₄s₃ = ∣ index , index-inc , index-path ∣
    where
    index : ℕ -> ℕ
    index = triangle-number

    index-inc : ∀ i -> index i < index (suc i)
    index-inc i = triangle-number-preserves-< refl-≤

    index-path : ∀ i -> partial-sums s₄ (triangle-number i) == partial-sums s₃ i
    index-path i = finiteMerge-triangle-encode₂ f i
