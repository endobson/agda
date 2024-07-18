{-# OPTIONS --cubical --safe --exact-split #-}

module real.caratheodory-derivative.identity where

open import base
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import real
open import real.caratheodory-derivative
open import real.metric-space
open import ring.implementations.real
open import semiring
open import subset
open import subset.subspace

private
  id : (Subspace (UnivS ℝ)) -> ℝ
  id (x , _) = x

isDerivative-id : isDerivative id (\_ -> 1#)
isDerivative-id .isDerivative.differentiable x∈@(x , _) = differentiable
  where
  slope-to : Subspace (UnivS ℝ) -> ℝ
  slope-to _ = 1#

  cont-slope-to : isContinuous slope-to
  cont-slope-to = isContinuous-const 1#

  differentiable : isDifferentiableAt id x∈
  differentiable .isDifferentiableAt.limit-point = isCrowded-ℝ x∈
  differentiable .isDifferentiableAt.slope-to = slope-to
  differentiable .isDifferentiableAt.isContinuousAt-slope-to =
    isContinuous.at cont-slope-to x∈
  differentiable .isDifferentiableAt.slope-to-path _ = *-left-one
isDerivative-id .isDerivative.derivative-path x∈@(x , _) = refl
