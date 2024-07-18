{-# OPTIONS --cubical --safe --exact-split #-}

module real.caratheodory-derivative.addition where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import real
open import real.caratheodory-derivative
open import real.continuous.arithmetic
open import ring.implementations.real
open import semiring
open import subset
open import subset.subspace

module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f g f' g' : Subspace S -> ℝ}
         (deriv-f : isDerivative f f') (deriv-g : isDerivative g g') where
  isDerivative-+ : isDerivative (\x -> f x + g x) (\x -> f' x + g' x)
  isDerivative-+ .isDerivative.differentiable x∈@(x , _) = differentiable
    where
    df : isDifferentiableAt f x∈
    df = isDerivative.differentiable deriv-f x∈
    dg : isDifferentiableAt g x∈
    dg = isDerivative.differentiable deriv-g x∈
    module df = isDifferentiableAt df
    module dg = isDifferentiableAt dg

    slope-to : Subspace S -> ℝ
    slope-to y∈ = df.slope-to y∈ + dg.slope-to y∈

    cont-slope-to : isContinuousAt slope-to x∈
    cont-slope-to = isContinuousAt-+ df.isContinuousAt-slope-to dg.isContinuousAt-slope-to

    slope-to-path : ∀ (y∈@(y , _) : Subspace S) ->
      slope-to y∈ * (diff x y) == diff (f x∈ + g x∈) (f y∈ + g y∈)
    slope-to-path y∈ =
      *-distrib-+-right >=>
      +-cong (df.slope-to-path y∈) (dg.slope-to-path y∈) >=>
      +-swap-diff

    differentiable : isDifferentiableAt (\x -> f x + g x) x∈
    differentiable .isDifferentiableAt.limit-point = df.limit-point
    differentiable .isDifferentiableAt.slope-to = slope-to
    differentiable .isDifferentiableAt.isContinuousAt-slope-to = cont-slope-to
    differentiable .isDifferentiableAt.slope-to-path = slope-to-path
  isDerivative-+ .isDerivative.derivative-path x∈ =
    +-cong (isDerivative.derivative-path deriv-f x∈) (isDerivative.derivative-path deriv-g x∈)
