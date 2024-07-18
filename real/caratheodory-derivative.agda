{-# OPTIONS --cubical --safe --exact-split #-}

module real.caratheodory-derivative where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import funext
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import metric-space.limit
open import real
open import real.continuous.arithmetic
open import real.continuous.arithmetic.multiplication
open import ring.implementations.real
open import semiring
open import subset
open import subset.subspace

module _ {ℓS : Level} {S : Subtype ℝ ℓS}  (f : Subspace S -> ℝ) (x∈@(x , _) : Subspace S) where
  record isDifferentiableAt : Type (ℓ-max ℓ-one ℓS)
    where
    field
      limit-point : isAccumulationPoint S x
      slope-to : Subspace S -> ℝ
      isContinuousAt-slope-to : isContinuousAt slope-to x∈
      slope-to-path : ∀ (y∈@(y , _) : Subspace S) -> slope-to y∈ * (diff x y) == diff (f x∈) (f y∈)

    derivative-at : ℝ
    derivative-at = slope-to x∈

module _ {ℓS : Level} {S : Subtype ℝ ℓS}  (f : Subspace S -> ℝ) where
  isDifferentiable : Type (ℓ-max ℓ-one ℓS)
  isDifferentiable = ∀ (x : Subspace S) -> isDifferentiableAt f x

record isDerivative {ℓS : Level} {S : Subtype ℝ ℓS} (f f' : Subspace S -> ℝ) : Type (ℓ-max ℓ-one ℓS) where
  field
    differentiable : isDifferentiable f
    derivative-path : ∀ x -> isDifferentiableAt.derivative-at (differentiable x) == f' x

module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f : Subspace S -> ℝ} where
  opaque
    isDifferentiable->isContinuous : isDifferentiable f -> isContinuous f
    isDifferentiable->isContinuous d .isContinuous.at x∈@(x , _) = c-f
      where
      module dx = isDifferentiableAt (d x∈)

      c-diff : isContinuous (\(y∈@(y , _) : Subspace S) -> diff x y)
      c-diff = (isContinuous-diff (isContinuous-const x) isContinuous-embed)

      c-fdiff : isContinuousAt (\y∈ -> diff (f x∈) (f y∈)) x∈
      c-fdiff = subst2 isContinuousAt (funExt dx.slope-to-path) (reflᵉ x∈) c-expr
        where
        c-expr : isContinuousAt (\(y∈@(y , _) : Subspace S) -> (dx.slope-to y∈) * diff x y) x∈
        c-expr = isContinuousAt-* dx.isContinuousAt-slope-to (isContinuous.at c-diff x∈)

      c-sum : isContinuousAt (\y∈ -> f x∈ + diff (f x∈) (f y∈)) x∈
      c-sum = isContinuousAt-+ c-fx c-fdiff
        where
        c-fx : isContinuousAt (\y∈ -> (f x∈)) x∈
        c-fx = isContinuous.at (isContinuous-const (f x∈)) x∈

      c-f : isContinuousAt f x∈
      c-f = subst2 isContinuousAt path (reflᵉ x∈) c-sum
        where
        path : (\y∈ -> f x∈ + diff (f x∈) (f y∈)) == f
        path = (funExt (\_ -> diff-step))
