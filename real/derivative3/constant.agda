{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative3.constant where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import funext
open import heyting-field.instances.real
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative3
open import real.derivative3.slope
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import ring.implementations.real
open import semiring
open import sequence
open import subset
open import subset.subspace
open import truncation

isDerivative-const : (k : ℝ) -> isDerivative (UnivS ℝ) (\_ -> k) (\_ -> 0#)
isDerivative-const k =
  isContinuousSlope->isDerivative (UnivS ℝ) NoIsolatedPoints-UnivS
    (\_ -> k) (\x y -> 0#)
    (\x -> isContinuous-const 0#)
    slope-const
  where
  slope-const : isSlope (UnivS ℝ) (\_ -> k) (\_ _ -> 0#)
  slope-const _ _ = *-left-zero >=> sym +-inverse
