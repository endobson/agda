{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2.identity where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import order.instances.real
open import ordered-semiring
open import ordered-additive-group.instances.real
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative2
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.limit-point
open import real.sequence.limit
open import funext
open import ring.implementations.real
open import semiring
open import truncation
open import subset
open import sequence
open import equivalence
open import ordered-additive-group


private
  id : Σ ℝ (\_ -> Top) -> ℝ
  id (x , _) = x

isDerivative-id : isDerivative (UnivS ℝ) id (\_ -> 1#)
isDerivative-id (x , _) .isDerivativeAt.limit-point = isLimitPoint-UnivS x
isDerivative-id (x , _) .isDerivativeAt.isLimit-∀seq t = lim
  where
  module t = LimitTestSeq t
  diff-seq : Sequence ℝ
  diff-seq i = diff (t.seq i) x * 1/diff (t.seq#x i)

  path : ∀ i -> 1# == diff-seq i
  path i = sym (ℝ1/-inverse _ _) >=> *-commute

  lim : isLimit diff-seq 1#
  lim = subst2 isLimit (funExt path) refl (isLimit-constant-seq 1#)
