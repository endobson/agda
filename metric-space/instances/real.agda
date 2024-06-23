{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.instances.real where

open import equivalence
open import additive-group
open import additive-group.instances.real
open import base
open import equality-path
open import metric-space
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-additive-group.minmax
open import real
open import isomorphism
open import ordered-additive-group

private
  disℝ : ℝ -> ℝ -> ℝ
  disℝ x y = abs (diff x y)

  opaque
    disℝ-commute : {x y : ℝ} -> disℝ x y == disℝ y x
    disℝ-commute = max-commute >=> cong2 max (sym diff-anticommute) diff-anticommute

    disℝ-triangle : {x y z : ℝ} -> (disℝ x z) ≤ (disℝ x y + disℝ y z)
    disℝ-triangle =
      trans-=-≤
        (cong2 max (sym diff-trans) (cong -_ (sym diff-trans) >=> minus-distrib-plus))
        max-+-swap

    path->zero-disℝ : {x y : ℝ} -> x == y -> disℝ x y == 0#
    path->zero-disℝ x=y =
      cong2 max (+-left (sym x=y) >=> +-inverse)
                (sym diff-anticommute >=> +-left x=y >=> +-inverse) >=>
      max-idempotent

    path<->zero-disℝ : {x y : ℝ} -> Iso (x == y) (disℝ x y == 0#)
    path<->zero-disℝ {x} {y} =
      isProp->iso path->zero-disℝ zero-disℝ->path
                  (isSet-ℝ _ _) (isSet-ℝ _ _)
      where
      zero-disℝ->path : (disℝ x y == 0#) -> x == y
      zero-disℝ->path dis-xy=0 = antisym-≤ x≤y y≤x
        where
        dxy≤0 : (diff x y) ≤ 0#
        dxy≤0 = trans-≤-= max-≤-left dis-xy=0
        dyx≤0 : (diff y x) ≤ 0#
        dyx≤0 = trans-=-≤ diff-anticommute (trans-≤-= max-≤-right dis-xy=0)
        x≤y : x ≤ y
        x≤y = diff-≤0⁻ dyx≤0
        y≤x : y ≤ x
        y≤x = diff-≤0⁻ dxy≤0

    isEquiv-path->zero-disℝ : {x y : ℝ} -> isEquiv (path->zero-disℝ {x} {y})
    isEquiv-path->zero-disℝ = isoToIsEquiv path<->zero-disℝ

instance
  MetricSpaceStr-ℝ : MetricSpaceStr ℝ
  MetricSpaceStr-ℝ = record
    { distance = disℝ
    ; 0≤distance = abs-0≤
    ; distance-commute = disℝ-commute
    ; distance-triangle = disℝ-triangle
    ; path->zero-distance = path->zero-disℝ
    ; isEquiv-path->zero-distance = isEquiv-path->zero-disℝ
    }
