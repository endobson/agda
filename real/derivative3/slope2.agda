{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative3.slope2 where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import heyting-field.instances.real
open import nat
open import metric-space
open import metric-space.instances.real
open import metric-space.instances.subspace
open import metric-space.continuous
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import rational
open import rational.order
open import real
open import real.derivative3
open import real.derivative3.slope
open import real.apartness
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.subspace
open import relation
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import subset.subspace
open import truncation
open import net
open import sum

ℚ#0-DirectedSet : DirectedSet ℓ-zero ℓ-zero
ℚ#0-DirectedSet .DirectedSet.Index = Σ[ q ∈ ℚ ] (q <> 0#)
ℚ#0-DirectedSet .DirectedSet.isSet-Index = isSetΣ isSetℚ (\_ -> isProp->isSet isProp-<>)
ℚ#0-DirectedSet .DirectedSet.R (q , _) (r , _) = abs q ≥ abs r
ℚ#0-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.isProp-≼ = isProp-≤
ℚ#0-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.refl-≼ = refl-≤
ℚ#0-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.trans-≼ lt1 lt2 = trans-≤ lt2 lt1
ℚ#0-DirectedSet .DirectedSet.isDirected-R .isDirected.∃upper-bound (q , q<>0) (r , r<>0) =
  ∣ (m , (inj-r (min-greatest-< 0<aq 0<ar))) , m≤aq , m≤ar ∣
  where
  m : ℚ
  m = min (abs q) (abs r)
  0<aq : 0# < abs q
  0<aq = either (\ q<0 -> trans-<-≤ (minus-flips-<0 q<0) max-≤-right)
                (\ 0<q -> trans-<-≤ 0<q max-≤-left) q<>0
  0<ar : 0# < abs r
  0<ar = either (\ r<0 -> trans-<-≤ (minus-flips-<0 r<0) max-≤-right)
                (\ 0<r -> trans-<-≤ 0<r max-≤-left) r<>0
  m≤aq : abs m ≤ abs q
  m≤aq = trans-=-≤ (abs-0≤-path (min-greatest-≤ abs-0≤ abs-0≤)) min-≤-left
  m≤ar : abs m ≤ abs r
  m≤ar = trans-=-≤ (abs-0≤-path (min-greatest-≤ abs-0≤ abs-0≤)) min-≤-right


private
  S : Subtype ℝ ℓ-zero
  S = UnivS ℝ

module _ {ℓS : Level}
         (f : Subspace (UnivS ℝ)-> ℝ) (f' : Subspace (UnivS ℝ) -> ℝ) (deriv : isDerivative (UnivS ℝ) f f')
         (x∈@(x , tt) : Subspace (UnivS ℝ))
         where

  s : (y : Subspace (ℝ#S' x)) -> ℝ
  s (y , x#y) = slope S f (x , tt) (y , tt) x#y

  sx : ℝ
  sx = f' (x , tt)

  n : Net (Subspace (ℝ#S' x)) ℓ-zero ℓ-zero
  n .Net.directed-set = ℚ#0-DirectedSet
  n .Net.f (q , q<>0) = (x + ℚ->ℝ q) , x#x+q
    where
    x#x+q : x # (x + ℚ->ℝ q)
    x#x+q =
      subst (_# (x + ℚ->ℝ q)) +-right-zero
        (sym-# (+₁-preserves-# (⊎-map ℚ->ℝ-preserves-< ℚ->ℝ-preserves-< q<>0)))



  -- isLimit-s : isLimitS (

  -- ans : ℝ
  -- ans = ?







  -- isDerivative->isContinuousSlope :
  --   Σ[ g ∈ (Subspace S -> Subspace S -> ℝ) ] (isSlope S f g)
  -- isDerivative->isContinuousSlope = ?
