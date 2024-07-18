{-# OPTIONS --cubical --safe --exact-split #-}

module real.caratheodory-derivative.constant where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
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

isDerivative-const : (k : ℝ) -> isDerivative (\(_ : Subspace (UnivS ℝ)) -> k) (\_ -> 0#)
isDerivative-const k .isDerivative.differentiable x∈@(x , _) = differentiable
  where
  slope-to : Subspace (UnivS ℝ) -> ℝ
  slope-to _ = 0#

  cont-slope-to : isContinuous slope-to
  cont-slope-to = isContinuous-const 0#

  differentiable : isDifferentiableAt (\(_ : Subspace (UnivS ℝ)) -> k) x∈
  differentiable .isDifferentiableAt.limit-point = isCrowded-ℝ x∈
  differentiable .isDifferentiableAt.slope-to = slope-to
  differentiable .isDifferentiableAt.isContinuousAt-slope-to =
    isContinuous.at cont-slope-to x∈
  differentiable .isDifferentiableAt.slope-to-path _ =
    *-left-zero >=> sym +-inverse
isDerivative-const k .isDerivative.derivative-path x∈@(x , _) = refl
