{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.point-line-apartness where

open import apartness
open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import cartesian-geometry
open import cartesian-geometry.line
open import cartesian-geometry.rotation
open import cartesian-geometry.semi-direction
open import cartesian-geometry.vector
open import order.instances.real
open import real
open import real.arithmetic.absolute-value
open import real.heyting-field
open import ring.implementations.real
open import hlevel
open import relation
open import vector-space.finite
open import vector-space
open import order
open import subset
open import funext
open import set-quotient

private

  same-semi-direction-distance : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
    semi-direction-distance d1 == semi-direction-distance d2
  same-semi-direction-distance d1 d2 (same-semi-direction-same p) =
    cong semi-direction-distance (direction-ext {d1} {d2} p)
  same-semi-direction-distance d1 d2 (same-semi-direction-flipped p) = funExt f
    where
    f : (v : Vector) -> semi-direction-distance d1 v == semi-direction-distance d2 v
    f v = cong absℝ dec1=-dec2 >=> absℝ-- _
      where
      d1=-d2 : d1 == (d- d2)
      d1=-d2 = direction-ext p

      dec1 : Axis -> ℝ
      dec1 = (basis-decomposition (isBasis-direction-basis d1) v)

      dec2 : Axis -> ℝ
      dec2 = (basis-decomposition (isBasis-direction-basis d2) v)

      check : dec1 x-axis == vector-index (rotate-vector (direction-diff d1 xaxis-dir) v) x-axis
      check = direction-basis-decomposition d1 v x-axis

      pd : (direction-diff d1 xaxis-dir) == add-half-rotation (direction-diff d2 xaxis-dir)
      pd = cong (\d -> direction-diff d xaxis-dir) d1=-d2 >=>
           direction-diff-minus-left _ _

      dec1=-dec2 : dec1 y-axis == - (dec2 y-axis)
      dec1=-dec2 =
        direction-basis-decomposition d1 v y-axis >=>
        cong (\v -> vector-index v y-axis)
          (cong (\r -> rotate-vector r v) pd >=>
           rotate-add-half-rotation (direction-diff d2 xaxis-dir) v) >=>
        cong -_ (sym (direction-basis-decomposition d2 v y-axis))

  semi-direction-distance' : SemiDirection -> Vector -> ℝ
  semi-direction-distance' =
    SemiDirectionElim.rec (isSetΠ \_ -> isSet-ℝ) semi-direction-distance same-semi-direction-distance

  semi-direction-distance'-v- : {v1 v2 : Vector} (sd : SemiDirection) -> v1 == (v- v2) ->
    semi-direction-distance' sd v1 == semi-direction-distance' sd v2
  semi-direction-distance'-v- {v1} {v2} =
    SemiDirectionElim.elimProp
      (\_ -> (isPropΠ (\_ -> isSet-ℝ _ _)))
      (\d -> semi-direction-distance-v- d {v1} {v2})

  same-semi-direction-span-comp : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
                                   (direction-span-comp d1) == (direction-span-comp d2)
  same-semi-direction-span-comp d1 d2 same-semi =
    same-Subtype (\{v} -> handle same-semi {v})
                 (\{v} -> handle (sym-SameSemiDirection same-semi) {v})
    where
    handle : {d1 d2 : Direction} -> SameSemiDirection d1 d2 -> {v : Vector} ->
             (direction-span'-comp d1 v) -> (direction-span'-comp d2 v)
    handle {d1} {d2} same {v} dis#0 =
      subst (\ sd -> semi-direction-distance' sd v # 0#) (eq/ d1 d2 same) dis#0

  semi-direction-span-comp : SemiDirection -> Subtype Vector ℓ-one
  semi-direction-span-comp sd v = semi-direction-distance' sd v # 0# , isProp-#



OffLine' : Line' -> Subtype Point ℓ-one
OffLine' (lp , sd) p = 0# < semi-direction-distance' sd (P-diff lp p) , isProp-< _ _

-- module _
--   where
--   OffLine'-SameLine' : (l1 l2 : Line') -> SameLine' l1 l2 -> OffLine' l1 == OffLine' l2
--   OffLine'-SameLine' l1 l2 (p2∈l1 , p1∈l2 , s1=s2) =
--     same-Subtype (f p1∈l2 s1=s2) (f p2∈l1 (sym s1=s2))
--     where
--     f : {l1 l2 : Line'} -> ⟨ OnLine' l2 (line'-point l1) ⟩ ->
--         line'-semi-direction l1 == line'-semi-direction l2 ->
--         {d : Point} -> ⟨ OffLine' l1 d ⟩ -> ⟨ OffLine' l2 d ⟩
--     f {p1 , s1} {p2 , s2} p1∈l2 s1=s2 {d} d∉l1 = ?
--
--
--   OffLine : Line -> Subtype Point ℓ-one
--   OffLine =
--     SetQuotientElim.rec Line' SameLine' isSet-Subtype OnLine' OnLine'-SameLine'
