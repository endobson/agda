{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2.constant where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import real
open import heyting-field.instances.real
open import real.arithmetic.multiplication.inverse
open import real.derivative2
open import real.sequence.harmonic
open import real.epsilon-bounded.base
open import real.rational
open import ring.implementations.real
open import semiring
open import subset
open import sequence
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import truncation
open import equivalence
open import funext

private
  const : ℝ -> Σ ℝ (\_ -> Top) -> ℝ
  const k _ = k


module _ (k : ℝ) where
  isDerivative-const : isDerivative (UnivS ℝ) (const k) (const 0#)
  isDerivative-const (x , _) .isDerivativeAt.limit-point = isLimitPoint-UnivS x
  isDerivative-const (x , _) .isDerivativeAt.isLimit-∀seq t = lim
    where
    module t = LimitTestSeq t
    diff-seq : Sequence ℝ
    diff-seq i = diff k k * (1/diff (t.seq#x i))

    path : ∀ i -> 0# == diff-seq i
    path i = sym *-left-zero >=> *-left (sym +-inverse)

    lim : isLimit diff-seq 0#
    lim = subst2 isLimit (funExt path) refl (isLimit-constant-seq 0#)
