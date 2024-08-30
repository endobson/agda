{-# OPTIONS --cubical --safe --exact-split #-}

module real.caratheodory-derivative where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import funext
open import hlevel.base
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import metric-space.limit
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import real
open import real.arithmetic.multiplication.inverse
open import real.continuous.arithmetic
open import real.continuous.arithmetic.multiplication
open import real.distance
open import ring.implementations.real
open import semiring
open import sigma.base
open import subset
open import subset.subspace
open import truncation

module _ {ℓS : Level} {S : Subtype ℝ ℓS} (f : Subspace S -> ℝ) (x∈@(x , _) : Subspace S) where
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

module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f : Subspace S -> ℝ} {x∈@(x , _) : Subspace S} where
  opaque
    isProp-isDifferentiableAt : isProp (isDifferentiableAt f x∈)
    isProp-isDifferentiableAt d1 d2 = d1=d2
      where
      module d1 = isDifferentiableAt d1
      module d2 = isDifferentiableAt d2

      same-slopes : d1.slope-to == d2.slope-to
      same-slopes = funExt (\y∈ -> tight-# (slopes-¬# y∈))
        where
        same-slopes-# : ∀ (y∈@(y , _) : Subspace S) -> x # y -> d1.slope-to y∈ == d2.slope-to y∈
        same-slopes-# y∈@(y , _) x#y =
          sym *-right-one >=>
          *-right (sym (ℝ1/-inverseᵉ (diff x y , d#0)) >=> *-commute) >=>
          sym *-assoc >=>
          *-left (d1.slope-to-path y∈ >=> sym (d2.slope-to-path y∈)) >=>
          *-assoc >=>
          *-right (*-commute >=> (ℝ1/-inverseᵉ (diff x y , d#0))) >=>
          *-right-one
          where
          d#0 : diff x y # 0#
          d#0 = case x#y of \{ (inj-l x<y) -> inj-r (diff-0<⁺ x<y) ;
                               (inj-r y<x) -> inj-l (diff-<0⁺ y<x) }

        slopes-diff : Subspace S -> ℝ
        slopes-diff y∈ = diff (d1.slope-to y∈) (d2.slope-to y∈)

        isLimitAt-sd : isLimitAt slopes-diff x (slopes-diff x∈)
        isLimitAt-sd =
          isContinuousAt->isLimitAt
            (isContinuousAt-diff d1.isContinuousAt-slope-to
                                 d2.isContinuousAt-slope-to)

        slopes-diff-# : ∀ (y∈@(y , _) : Subspace S) -> x # y -> slopes-diff y∈ == 0#
        slopes-diff-# y∈ x#y =
          cong2 diff (same-slopes-# y∈ x#y) refl >=>
          +-inverse

        isPuncturedLimitAt-sd : isPuncturedLimitAt slopes-diff x 0#
        isPuncturedLimitAt-sd .isPuncturedLimitAt.limit-point = d1.limit-point
        isPuncturedLimitAt-sd .isPuncturedLimitAt.close ε@(_ , 0<ε) = ∣ (ε , close') ∣
          where
          close' : ∀ y∈ -> 0# < distance x∈ y∈ -> εClose ε x∈ y∈ -> εClose ε 0# (slopes-diff y∈)
          close' y∈@(y , _) 0<d _ =
            trans-=-< (path->zero-distance (sym (slopes-diff-# y∈ x#y))) 0<ε
            where
            x#y : x # y
            x#y = metric#-># 0<d

        sdx=0 : slopes-diff x∈ == 0#
        sdx=0 = isLimitAt=isPuncturedLimitAt isLimitAt-sd isPuncturedLimitAt-sd

        same-slopes-x : d1.slope-to x∈ == d2.slope-to x∈
        same-slopes-x = sym +-right-zero >=> +-right (sym sdx=0) >=> diff-step


        slopes-¬# : ∀ y∈ -> ¬ (d1.slope-to y∈ # d2.slope-to y∈)
        slopes-¬# y∈@(y , _) s1#s2 =
          irrefl-path-# (cong d1.slope-to (sym x=y) >=>
                         same-slopes-x >=>
                         cong d2.slope-to x=y) s1#s2
          where
          x=y : x∈ == y∈
          x=y = Subspace-path (tight-# (\x#y -> irrefl-path-# (same-slopes-# y∈ x#y) s1#s2))

      d1=d2 : d1 == d2
      d1=d2 i .isDifferentiableAt.limit-point =
        isProp-isAccumulationPoint d1.limit-point d2.limit-point i
      d1=d2 i .isDifferentiableAt.slope-to = same-slopes i
      d1=d2 i .isDifferentiableAt.isContinuousAt-slope-to =
        isProp->PathPᵉ (\i -> isProp-isContinuousAt (same-slopes i))
          d1.isContinuousAt-slope-to
          d2.isContinuousAt-slope-to
          i
      d1=d2 i .isDifferentiableAt.slope-to-path =
        isProp->PathPᵉ
          (\i -> isPropΠ (\y∈ -> isSet-ℝ (same-slopes i y∈ * _) _))
          d1.slope-to-path
          d2.slope-to-path
          i

module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f : Subspace S -> ℝ} where
  opaque
    isProp-isDifferentiable : isProp (isDifferentiable f)
    isProp-isDifferentiable = isPropΠ (\_ -> isProp-isDifferentiableAt)

module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f f' : Subspace S -> ℝ} where
  opaque
    isProp-isDerivative : isProp (isDerivative f f')
    isProp-isDerivative d1 d2 = (\i -> record
      { differentiable = dp i
      ; derivative-path =
        isProp->PathPᵉ (\i -> isPropΠ (\y -> isSet-ℝ (isDifferentiableAt.derivative-at (dp i y)) _))
          d1.derivative-path
          d2.derivative-path
          i
      })
      where
      module d1 = isDerivative d1
      module d2 = isDerivative d2

      dp : d1.differentiable == d2.differentiable
      dp = isProp-isDifferentiable (isDerivative.differentiable d1)
                                   (isDerivative.differentiable d2)

module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f : Subspace S -> ℝ} where
  opaque
    isProp-ΣisDerivative : isProp (Σ (Subspace S -> ℝ) (isDerivative f))
    isProp-ΣisDerivative (g1 , d1) (g2 , d2) =
      ΣProp-path isProp-isDerivative g1=g2
      where
      module d1 = isDerivative d1
      module d2 = isDerivative d2

      d-path : d1.differentiable == d2.differentiable
      d-path = isProp-isDifferentiable _ _

      g1=g2 : g1 == g2
      g1=g2 = funExt (\x -> sym (d1.derivative-path x) >=>
                            (\i -> isDifferentiableAt.derivative-at (d-path i x)) >=>
                            d2.derivative-path x)


module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f : Subspace S -> ℝ} where

  opaque
    isDifferentiableAt->isContinuousAt :
      {x∈ : Subspace S} -> isDifferentiableAt f x∈ -> isContinuousAt f x∈
    isDifferentiableAt->isContinuousAt {x∈@(x , _)} dx = c-f
      where
      module dx = isDifferentiableAt dx

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

    isDifferentiable->isContinuous : isDifferentiable f -> isContinuous f
    isDifferentiable->isContinuous d .isContinuous.at x∈ =
      isDifferentiableAt->isContinuousAt (d x∈)
