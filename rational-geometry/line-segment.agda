{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.line-segment where

open import base
open import order
open import equivalence
open import additive-group
-- TODO make this exist
-- open import additive-group.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import order.minmax.instances.rational
open import ordered-semiring
open import ordered-ring.absolute-value
open import ordered-semiring.instances.rational
open import ring.implementations.rational
open import relation
open import set-quotient
open import order.instances.rational
open import equality-path
open import semiring
open import rational
-- TODO Put the instances in the instances file even if the definition is also here
open import rational.order
open import rational-geometry.point
open import rational-geometry.direction
open import rational-geometry.line

record LineSegment : Type ℓ-zero where
  constructor line-segment
  field
    p₁ p₂ : Point
    p₁!=p₂ : p₁ != p₂

north : Direction
north = direction 0# 1# (+-cong (abs-0≤-path refl-≤) (abs-0≤-path 0≤1) >=> +-left-zero)
south : Direction
south = direction 0# (- 1#) (+-cong (abs-0≤-path refl-≤) (abs-minus >=> abs-0≤-path 0≤1) >=> +-left-zero)
east : Direction
east = direction 1# 0# (+-cong (abs-0≤-path 0≤1) (abs-0≤-path refl-≤) >=> +-right-zero)
west : Direction
west = direction (- 1#) 0# (+-cong (abs-minus >=> abs-0≤-path 0≤1) (abs-0≤-path refl-≤) >=> +-right-zero)


line-segment-L¹distance : LineSegment -> ℚ
line-segment-L¹distance (line-segment (x₁ , y₁) (x₂ , y₂) _) =
  abs (diff x₁ x₂) + abs (diff y₁ y₂)

line-segment->direction : LineSegment -> Direction
line-segment->direction (line-segment (x₁ , y₁) (x₂ , y₂) ne) =
  handle (trichotomous-< x₁ x₂) (trichotomous-< y₁ y₂)
  where
  normalized-direction : (dx : ℚ) -> (dx <> 0#) -> (dy : ℚ) -> (dy <> 0#) -> Direction
  normalized-direction dx dx<>0 dy dy<>0 =
    direction (dx * r1/ denom denom!=0) (dy * r1/ denom denom!=0) path
    where
    0<adx : 0# < abs dx
    0<adx = eqFun abs-#0-eq dx<>0
    0<ady : 0# < abs dy
    0<ady = eqFun abs-#0-eq dy<>0

    denom : ℚ
    denom = abs dx + abs dy

    0<denom : 0# < denom
    0<denom = +-preserves-0< 0<adx 0<ady

    denom!=0 : denom != 0#
    denom!=0 p = irrefl-path-< (sym p) 0<denom

    path : abs (dx * r1/ denom denom!=0) + abs (dy * r1/ denom denom!=0) == 1#
    path =
      +-cong abs-distrib-* abs-distrib-* >=>
      sym *-distrib-+-right >=>
      *-right (abs-0<-path (r1/-preserves-Pos _ _ 0<denom)) >=>
      *-commute >=>
      r1/-inverse denom denom!=0

  handle : Tri< x₁ x₂ -> Tri< y₁ y₂ -> Direction
  handle (tri= _  xp _ ) (tri= _  yp _ ) = bot-elim (ne (\i -> xp i , yp i))
  handle (tri= _  _  _ ) (tri< _  _  _ ) = north
  handle (tri= _  _  _ ) (tri> _  _  _ ) = south
  handle (tri< _  _  _ ) (tri= _  _  _ ) = east
  handle (tri> _  _  _ ) (tri= _  _  _ ) = west
  handle (tri< dx _  _ ) (tri< dy _  _ ) = normalized-direction (diff x₁ x₂) (inj-r (diff-0<⁺ dx))
                                                                (diff y₁ y₂) (inj-r (diff-0<⁺ dy))
  handle (tri< dx _  _ ) (tri> _  _  dy) = normalized-direction (diff x₁ x₂) (inj-r (diff-0<⁺ dx))
                                                                (diff y₁ y₂) (inj-l (diff-<0⁺ dy))
  handle (tri> _  _  dx) (tri< dy _  _ ) = normalized-direction (diff x₁ x₂) (inj-l (diff-<0⁺ dx))
                                                                (diff y₁ y₂) (inj-r (diff-0<⁺ dy))
  handle (tri> _  _  dx) (tri> _  _  dy) = normalized-direction (diff x₁ x₂) (inj-l (diff-<0⁺ dx))
                                                                (diff y₁ y₂) (inj-l (diff-<0⁺ dy))

line-segment->line : LineSegment -> Line
line-segment->line l@(line-segment p₁ _ _) = [ line' p₁ (line-segment->direction l) ]
