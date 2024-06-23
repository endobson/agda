{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space where

open import additive-group
open import additive-group.instances.real
open import base
open import equivalence.base
open import order
open import order.instances.real
open import real

private
  variable
    ℓ : Level

record MetricSpaceStr (D : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ-zero)) where
  no-eta-equality
  field
    distance : D -> D -> ℝ
    0≤distanceᵉ : (x y : D) -> 0# ≤ distance x y
    distance-commuteᵉ : (x y : D) -> distance x y == distance y x
    distance-triangleᵉ : (x y z : D) -> distance x z ≤ (distance x y + distance y z)
    path->zero-distance : {x y : D} -> x == y -> distance x y == 0#
    isEquiv-path->zero-distance : {x y : D} -> isEquiv (path->zero-distance {x} {y})


module _ {D : Type ℓ} {{MS : MetricSpaceStr D}} where
  open MetricSpaceStr MS public

  0≤distance : {x y : D} -> 0# ≤ distance x y
  0≤distance = 0≤distanceᵉ _ _

  distance-commute : {x y : D} -> distance x y == distance y x
  distance-commute = distance-commuteᵉ _ _

  distance-triangle : {x y z : D} -> distance x z ≤ (distance x y + distance y z)
  distance-triangle = distance-triangleᵉ _ _ _
