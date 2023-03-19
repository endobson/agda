{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponetial-series2 where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import factorial
open import integral-domain.instances.real
open import nat
open import order
open import order.instances.rational
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-integral-domain
open import ordered-semiring.archimedean
open import ordered-semiring.instances.real
open import rational
open import rational.integral-domain
open import rational.order
open import real
open import real.arithmetic.rational
open import real.rational
open import real.series
open import ring.implementations.real
open import semiring
open import semiring.initial
open import sequence
open import sequence.partial-sums
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

  ℝ^ℕ : ℝ -> ℕ -> ℝ
  ℝ^ℕ x zero = 1#
  ℝ^ℕ x (suc n) = x * (ℝ^ℕ x n)

  exponential-sequence : ℝ -> Seq
  exponential-sequence x n = (ℝ^ℕ x n) * ℚ->ℝ (1/ℕ (factorial⁺ n))

  exponential-series : ℝ -> Seq
  exponential-series x = partial-sums (exponential-sequence x)

module _
  {{ArchimedeanSemring-ℝ : ArchimedeanSemiringⁱ ℝ}}
  where

  private
    ℝFinite : (x : ℝ) -> ∃[ n ∈ ℕ ] (x < ℕ->ℝ n)
    ℝFinite x = ∥-bind handle (Real.located x _ _ 0<1)
      where
      handle : (Real.L x 0# ⊎ Real.U x 1#) -> ∃[ n ∈ ℕ ] (x < ℕ->ℝ n)
      handle (inj-r xU-1) = ∣ 1 , U->ℝ< xU-1 ∣
      handle (inj-l xL-0) = ∥-map handle2 (archimedean-property (L->ℝ< xL-0) 0<1)
        where
        handle2 : Σ[ n ∈ ℕ ] (x < (ℕ->Semiring n * 1#)) -> Σ[ n ∈ ℕ ] (x < ℕ->ℝ n)
        handle2 (n , x<n1) = n , trans-<-= x<n1 (*-right-one >=> ℕ->Semiring-ℝ-path n)

  -- exponential-sequence<geometric-sequence : (x : ℝ) ->
  --   ∀Largeℕ (\n -> exponential-sequence x n < geometric-sequence 1/2ℝ n)
  -- exponential-sequence<geometric-sequence = ∥-map handle (archimedean-property
