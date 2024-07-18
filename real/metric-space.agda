{-# OPTIONS --cubical --safe --exact-split #-}

module real.metric-space where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import heyting-field.instances.real
open import metric-space
open import metric-space.instances.real
open import metric-space.limit
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.distance
open import ring.implementations.real
open import semiring
open import subset
open import subset.subspace
open import truncation

opaque
  isCrowded-ℝ : isCrowded (UnivS ℝ)
  isCrowded-ℝ (x , _) .isAccumulationPoint.close (ε , 0<ε) =
    ∣ (y , tt) , 0<dxy , dxy<ε ∣
    where
    ε' : ℝ
    ε' = 1/2 * ε
    0<ε' : 0# < ε'
    0<ε' = (*-preserves-0< 0<1/2 0<ε)
    y : ℝ
    y = x + ε'
    dxy=ε' : distance x y == ε'
    dxy=ε' = distance-shift >=> (abs-0≤-path (weaken-< 0<ε'))
    0<dxy : 0# < distance x y
    0<dxy = trans-<-= 0<ε' (sym dxy=ε')
    dxy<ε : distance x y < ε
    dxy<ε = subst2 _<_ (sym dxy=ε') *-left-one (*₂-preserves-< 1/2<1 0<ε)
