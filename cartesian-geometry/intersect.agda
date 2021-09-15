{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.intersect where

open import apartness
open import base
open import cartesian-geometry
open import cartesian-geometry.line
open import cartesian-geometry.vector
open import cubical
open import equality
open import equivalence
open import functions
open import funext
open import heyting-field
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import isomorphism
open import order
open import real
open import real.arithmetic.absolute-value
open import real.heyting-field
open import ring
open import ring.implementations.real
open import semiring
open import set-quotient
open import vector-space
open import vector-space.finite

private
  abstract
    direction->isUnit-y : (d : Direction) -> semi-direction-distance d xaxis-vector # 0# ->
                          Ring.isUnit ℝRing (vector-index ⟨ d ⟩ y-axis)
    direction->isUnit-y d@(dv , _) abs-d#axis = isUnit-y
      where
      d#axis : (basis-decomposition (isBasis-rotated-basis d) xaxis-vector y-axis) # 0#
      d#axis = (eqFun (<>-equiv-# _ _) (absℝ-#0 _ (eqInv (<>-equiv-# _ _) abs-d#axis)))

      d-path : (basis-decomposition (isBasis-rotated-basis d) xaxis-vector) ==
               (vector-index ⟨ (conjugate-direction d) ⟩ )
      d-path = cong vector-index (rotated-basis-x-axis (conjugate-direction d))

      d#axis2 : (- (vector-index dv y-axis)) # 0#
      d#axis2 = subst (\x -> x y-axis # 0#) d-path d#axis

      d#axis3 : (vector-index dv y-axis) # 0#
      d#axis3 = subst2 _#_ minus-double-inverse minus-zero (minus-reflects-# d#axis2)

      isUnit-y : Ring.isUnit ℝRing (vector-index dv y-axis)
      isUnit-y = Field.#0->isUnit ℝField d#axis3


  direction->run/rise : (d : Direction) -> semi-direction-distance d xaxis-vector # 0# -> ℝ
  direction->run/rise d@(dv , _) d#0 =
    (vector-index dv x-axis) * (Ring.isUnit.inv (direction->isUnit-y d d#0))

  semi-direction->run/rise :
    (sd : SemiDirection) -> semi-direction-distance' sd xaxis-vector # 0# -> ℝ
  semi-direction->run/rise =
    SemiDirectionElim.elim (\_ -> isSetΠ (\_ -> isSet-ℝ)) direction->run/rise
      (\d1 d2 same-d -> funExtDep d1 d2 (same same-d))
    where
    same : {d1 d2 : Direction} -> SameSemiDirection d1 d2 ->
           (b1 : semi-direction-distance d1 xaxis-vector # 0#) ->
           (b2 : semi-direction-distance d2 xaxis-vector # 0#) ->
           direction->run/rise d1 b1 ==
           direction->run/rise d2 b2
    same {d1} {d2} (same-semi-direction-same dv-path) b1 b2 =
      cong2-dep direction->run/rise (direction-ext dv-path)
                (isProp->PathP (\i -> isProp-#) b1 b2)
    same {d1} {d2} (same-semi-direction-flipped dv-path) b1 b2 =
      *-left (cong (\v -> vector-index v x-axis) dv-path) >=>
      minus-extract-left >=> sym minus-extract-right >=>
      *-right i-path
      where
      d1x = vector-index ⟨ d1 ⟩ x-axis
      d1y = vector-index ⟨ d1 ⟩ y-axis
      d2x = vector-index ⟨ d2 ⟩ x-axis
      d2y = vector-index ⟨ d2 ⟩ y-axis
      u1 = direction->isUnit-y d1 b1
      -u1 : Ring.isUnit ℝRing (- (vector-index ⟨ d1 ⟩ y-axis))
      -u1 = Ring.u--closed ℝRing u1
      u2 = direction->isUnit-y d2 b2

      y-path : (- d1y) == d2y
      y-path = cong (\v -> (- (vector-index v y-axis))) dv-path >=> minus-double-inverse

      u-path : PathP (\i -> Ring.isUnit ℝRing (y-path i)) -u1 u2
      u-path = isProp->PathP (\i -> Ring.isProp-isUnit ℝRing) -u1 u2

      i-path : - (Ring.isUnit.inv u1) == (Ring.isUnit.inv u2)
      i-path i = Ring.isUnit.inv (u-path i)



  semi-direction->unit-rise :
    (sd : SemiDirection) -> semi-direction-distance' sd xaxis-vector # 0# -> Vector
  semi-direction->unit-rise sd sd#0 =
    vector-cons (\{x-axis -> semi-direction->run/rise sd sd#0 ; y-axis -> 1#})

  direction->unit-rise : (d : Direction) -> semi-direction-distance d xaxis-vector # 0# -> Vector
  direction->unit-rise d d#0 = semi-direction->unit-rise [ d ] d#0

  direction->unit-rise-on-span :
    (d : Direction) -> (d#0 : semi-direction-distance d xaxis-vector # 0#) ->
    ⟨ direction-span d (direction->unit-rise d d#0) ⟩
  direction->unit-rise-on-span d@(dv , _) d#0 =
    Ring.isUnit.inv Uy ,
    vector-ext (\ { x-axis -> *-commute
                  ; y-axis -> *-commute >=> Ring.isUnit.path Uy
                  })
    where
    Uy = direction->isUnit-y d d#0


  semi-direction->unit-rise-on-span :
    (sd : SemiDirection) -> (sd#0 : semi-direction-distance' sd xaxis-vector # 0#) ->
    ⟨ semi-direction-span sd (semi-direction->unit-rise sd sd#0) ⟩
  semi-direction->unit-rise-on-span =
    SemiDirectionElim.elimProp
      (\ sd -> isPropΠ (\sd#0 -> snd (semi-direction-span sd (semi-direction->unit-rise sd sd#0))))
      direction->unit-rise-on-span


  point-direction->x-intercept :
    (p : Point) (d : Direction) -> semi-direction-distance d xaxis-vector # 0# -> Point
  point-direction->x-intercept p d d#0 =
    P-shift p ((- (Point.y p)) v* (direction->unit-rise d d#0))

  point-direction->x-intercept-on-axis :
    (p : Point) (d : Direction) -> (d#0 : semi-direction-distance d xaxis-vector # 0#) ->
    Point.y (point-direction->x-intercept p d d#0) == 0#
  point-direction->x-intercept-on-axis p d d#0 = +-right *-right-one >=> +-inverse

  point-direction->x-intercept-on-span :
    (p : Point) (d : Direction) -> (d#0 : semi-direction-distance d xaxis-vector # 0#) ->
    ⟨ direction-span d (P-diff p (point-direction->x-intercept p d d#0)) ⟩
  point-direction->x-intercept-on-span p d d#0 =
    (- (Point.y p)) * fst unit-rise-on-span ,
    v*-assoc >=> v*-right (snd unit-rise-on-span) >=> sym v-path
    where
    v-path : (P-diff p (point-direction->x-intercept p d d#0)) ==
             ((- (Point.y p)) v* (direction->unit-rise d d#0))
    v-path = P-shift-step p ((- (Point.y p)) v* (direction->unit-rise d d#0))

    unit-rise-on-span = direction->unit-rise-on-span d d#0


  point-semi-direction->x-intercept :
    (p : Point) (sd : SemiDirection) -> semi-direction-distance' sd xaxis-vector # 0# -> Point
  point-semi-direction->x-intercept p sd sd#0 =
    P-shift p ((- (Point.y p)) v* (semi-direction->unit-rise sd sd#0))


  point-semi-direction->x-intercept-on-axis :
    (p : Point) (sd : SemiDirection) -> (sd#0 : semi-direction-distance' sd xaxis-vector # 0#) ->
    Point.y (point-semi-direction->x-intercept p sd sd#0) == 0#
  point-semi-direction->x-intercept-on-axis p sd sd#0 = +-right *-right-one >=> +-inverse

  point-semi-direction->x-intercept-on-span :
    (p : Point) (sd : SemiDirection) -> (sd#0 : semi-direction-distance' sd xaxis-vector # 0#) ->
    ⟨ semi-direction-span sd (P-diff p (point-semi-direction->x-intercept p sd sd#0)) ⟩
  point-semi-direction->x-intercept-on-span p =
    SemiDirectionElim.elimProp
      (\sd -> isPropΠ (\sd#0 -> snd (semi-direction-span sd
                                      (P-diff p (point-semi-direction->x-intercept p sd sd#0)))))
      (point-direction->x-intercept-on-span p)

  point-direction->OnLine' :
    (p : Point) (d : Direction) -> (d#0 : semi-direction-distance d xaxis-vector # 0#) ->
    ⟨ OnLine' (p , [ d ]) (point-direction->x-intercept p d d#0) ⟩
  point-direction->OnLine' p d d#0 = point-direction->x-intercept-on-span p d d#0

  point-semi-direction->OnLine' :
    (p : Point) (sd : SemiDirection) -> (sd#0 : semi-direction-distance' sd xaxis-vector # 0#) ->
    ⟨ OnLine' (p , sd) (point-semi-direction->x-intercept p sd sd#0) ⟩
  point-semi-direction->OnLine' p sd sd#0 = point-semi-direction->x-intercept-on-span p sd sd#0
