{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.glue-point where

open import base
open import additive-group
open import additive-group.instances.real
open import metric-space
open import metric-space.continuous
open import metric-space.complete
open import metric-space.instances.subspace
open import subset
open import subset.subspace
open import real
open import rational
open import order.instances.rational
open import order
open import net
open import order.instances.real
open import hlevel
open import truncation
open import order.minmax
open import order.minmax.instances.rational

ℚ⁺-DirectedSet : DirectedSet ℓ-zero ℓ-zero
ℚ⁺-DirectedSet .DirectedSet.Index = ℚ⁺
ℚ⁺-DirectedSet .DirectedSet.isSet-Index = isSetΣ isSetℚ (\_ -> isProp->isSet isProp-<)
ℚ⁺-DirectedSet .DirectedSet.R (q , _) (r , _) = q ≥ r
ℚ⁺-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.isProp-≼ = isProp-≤
ℚ⁺-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.refl-≼ = refl-≤
ℚ⁺-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.trans-≼ lt1 lt2 = trans-≤ lt2 lt1
ℚ⁺-DirectedSet .DirectedSet.isDirected-R .isDirected.∃upper-bound (q , 0<q) (r , 0<r) =
  ∣ (min q r , min-greatest-< 0<q 0<r) , min-≤-left , min-≤-right ∣


module _ {ℓA : Level} {A : Type ℓA} {{MS-A : MetricSpaceStr A}} where
  Metric<>S : (a : A) -> Subtype A ℓ-one
  Metric<>S a x = 0# < distance a x , isProp-<

module _
  {ℓA ℓB ℓS ℓI ℓ≼ : Level}
  {A : Type ℓA} {B : Type ℓB}
  {{MS-A : MetricSpaceStr A}} {{MS-B : MetricSpaceStr B}}
  (a : A)
  (f : (x : Subspace (Metric<>S a)) -> B)
  ((isContinuous-cons cf) : isContinuous f)
  {lim : B}
  (isLimit-lim : isLimitAt f a lim ℓI ℓ≼)
  (isLimit₀-lim : isLimitAt f a lim ℓ-zero ℓ-zero)
  (isComplete-B : isComplete B ℓI ℓ≼)
  (isComplete₀-B : isComplete₀ B)
  (x : A)
  (magic : Magic)
  where

  n : Net B ℓ-zero ℓ-zero
  n .Net.directed-set = ℚ⁺-DirectedSet
  n .Net.f (q , 0<q) = distance



  extend-<> : B
  extend-<> = fst (isComplete₀-B n magic)
