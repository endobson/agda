{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative3.identity where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import order
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order.instances.real
open import ordered-semiring
open import ordered-additive-group.instances.real
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative3
open import real.derivative3.slope
open import real.derivative3.constant
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.limit-point
open import real.sequence.limit
open import funext
open import ring.implementations.real
open import semiring
open import truncation
open import subset
open import subset.subspace
open import sequence
open import equivalence
open import ordered-additive-group


private
  id : (Subspace (UnivS ℝ)) -> ℝ
  id (x , _) = x

isDerivative-id : isDerivative (UnivS ℝ) id (\_ -> 1#)
isDerivative-id =
  isContinuousSlope->isDerivative (UnivS ℝ) NoIsolatedPoints-UnivS
    id (\x y -> 1#)
    (\x -> isContinuous-const 1#)
    slope-id
  where
  slope-id : isSlope (UnivS ℝ) id (\_ _ -> 1#)
  slope-id _ _ = *-left-one
