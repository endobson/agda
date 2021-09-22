{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.intersect where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry
open import cartesian-geometry.line
open import cartesian-geometry.rotation
open import cartesian-geometry.semi-direction
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
open import sigma
open import subset
open import vector-space
open import vector-space.finite

private
  abstract
    direction->y#0 : (d : Direction) -> semi-direction-distance d xaxis-vector # 0# ->
                          (vector-index ⟨ d ⟩ y-axis) # 0#
    direction->y#0 d@(dv , _) abs-d#axis = d#axis3
      where
      d#axis : (basis-decomposition (isBasis-rotated-basis (rotation d)) xaxis-vector y-axis) # 0#
      d#axis = (eqFun (<>-equiv-# _ _) (absℝ-#0 _ (eqInv (<>-equiv-# _ _) abs-d#axis)))

      d-path : (basis-decomposition (isBasis-rotated-basis (rotation d)) xaxis-vector) ==
               (vector-index ⟨ (conjugate-direction d) ⟩ )
      d-path = cong vector-index (rotated-basis-x-axis (r- (rotation d)))

      d#axis2 : (- (vector-index dv y-axis)) # 0#
      d#axis2 = subst (\x -> x y-axis # 0#) d-path d#axis

      d#axis3 : (vector-index dv y-axis) # 0#
      d#axis3 = subst2 _#_ minus-double-inverse minus-zero (minus-reflects-# d#axis2)

    direction->isUnit-y : (d : Direction) -> semi-direction-distance d xaxis-vector # 0# ->
                          Ring.isUnit ℝRing (vector-index ⟨ d ⟩ y-axis)
    direction->isUnit-y d d#0 = Field.#0->isUnit ℝField (direction->y#0 d d#0)


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

  point-direction->x-intercept-on-axis' :
    (p : Point) (d : Direction) -> (d#0 : semi-direction-distance d xaxis-vector # 0#) ->
    ⟨ direction-span xaxis-dir (P-diff 0P (point-direction->x-intercept p d d#0)) ⟩
  point-direction->x-intercept-on-axis' p d d#0 = vx , vx-path
    where
    v = (P-diff 0P (point-direction->x-intercept p d d#0))
    vx = vector-index v x-axis
    abstract
      vx-path : vx v* xaxis-vector == v
      vx-path = vector-ext f
        where
        f : (a : Axis) -> vector-index (vx v* xaxis-vector) a == vector-index v a
        f x-axis = *-right-one
        f y-axis = *-right-zero >=> sym +-right-zero >=> +-right (sym minus-zero) >=>
                   +-left (sym (point-direction->x-intercept-on-axis p d d#0))


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

  module _ (lp : Point) (d : Direction) (d#0 : semi-direction-distance d xaxis-vector # 0#)
    where
    private
      on-axis : Subtype Point ℓ-one
      on-axis p = direction-span xaxis-dir (P-diff 0P p)
      on-span : Subtype Point ℓ-one
      on-span p = direction-span d (P-diff lp p)

    isProp-x-intercept : isProp (Σ[ p ∈ Point ] (⟨ on-span p ⟩ × ⟨ on-axis p ⟩))
    isProp-x-intercept (p1 , (sk1 , sp1) , a1@(ak1 , ap1)) (p2 , (sk2 , sp2) , a2@(ak2 , ap2)) =
      ΣProp-path (\{p} -> isProp× (snd (on-span p)) (snd (on-axis p))) p1=p2
      where
      ya-path : (p : Point) -> ⟨ on-axis p ⟩ -> P-coord p y-axis == 0#
      ya-path p (_ , ap) =
        sym +-right-zero >=> +-right (sym minus-zero) >=>
        sym (cong (\v -> vector-index v y-axis) ap) >=>
        *-right-zero

      diff-path : (diff sk1 sk2) v* ⟨ d ⟩ == P-diff p1 p2
      diff-path = sym step1 >=> step2 >=> step3
        where
        step2 : (v- (sk1 v* ⟨ d ⟩)) v+ (sk2 v* ⟨ d ⟩) == (v- (P-diff lp p1)) v+ (P-diff lp p2)
        step2 = cong2 _v+_ (cong v-_ sp1) sp2

        step3 : (v- (P-diff lp p1)) v+ (P-diff lp p2) == P-diff p1 p2
        step3 = v+-left (sym (P-diff-anticommute p1 lp)) >=> P-diff-trans p1 lp p2

        step1 : (v- (sk1 v* ⟨ d ⟩)) v+ (sk2 v* ⟨ d ⟩) == (diff sk1 sk2) v* ⟨ d ⟩
        step1 = v+-left (sym v*-minus-extract-left) >=>
                v+-commute >=>
                sym v*-distrib-+

      diff0s-path : (diff sk1 sk2) == 0#
      diff0s-path = *₂-reflects-= (direction->y#0 d d#0) path3
        where
        path1 : (diff sk1 sk2) * (vector-index ⟨ d ⟩ y-axis) ==
                vector-index (P-diff p1 p2) y-axis
        path1 = cong (\v -> vector-index v y-axis) diff-path

        path2 : (diff sk1 sk2) * (vector-index ⟨ d ⟩ y-axis) == 0#
        path2 = path1 >=> +-cong (ya-path p2 a2) (cong -_ (ya-path p1 a1)) >=> +-inverse

        path3 : (diff sk1 sk2) * (vector-index ⟨ d ⟩ y-axis) == 0# * (vector-index ⟨ d ⟩ y-axis)
        path3 = path2 >=> sym *-left-zero


      diff0p-path : P-diff p1 p2 == 0v
      diff0p-path = sym diff-path >=> v*-left diff0s-path >=> v*-left-zero

      p1=p2 : p1 == p2
      p1=p2 = sym (P-shift-0v p1) >=> cong (P-shift p1) (sym diff0p-path) >=> (P-diff-step p1 p2)

    point-direction->x-intercept-full : isContr (Σ[ p ∈ Point ] (⟨ on-span p ⟩ × ⟨ on-axis p ⟩))
    point-direction->x-intercept-full =
      (point-direction->x-intercept lp d d#0 ,
       point-direction->x-intercept-on-span lp d d#0 ,
       point-direction->x-intercept-on-axis' lp d d#0) ,
      isProp-x-intercept _



  point-semi-direction->x-intercept :
    (p : Point) (sd : SemiDirection) -> semi-direction-distance' sd xaxis-vector # 0# -> Point
  point-semi-direction->x-intercept p sd sd#0 =
    P-shift p ((- (Point.y p)) v* (semi-direction->unit-rise sd sd#0))


  point-semi-direction->x-intercept-full :
    (lp : Point) (sd : SemiDirection) ->
    isContr (
      semi-direction-distance' sd xaxis-vector # 0# ->
      Σ[ p ∈ Point ] (⟨ semi-direction-span sd (P-diff lp p) ⟩ ×
                      ⟨ semi-direction-span xaxis-semi-dir (P-diff 0P p) ⟩))
  point-semi-direction->x-intercept-full lp =
    SemiDirectionElim.liftContr (\ d -> isContrΠ (\ d#0 -> point-direction->x-intercept-full lp d d#0))





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




  line'->x-intercept :
    (l : Line') -> (line'-semi-direction l) sd# xaxis-semi-dir -> Point
  line'->x-intercept (p , sd) l#a = point-semi-direction->x-intercept p sd l#a

  line'->x-intercept-on-line' :
    (l : Line') -> (l#x : (line'-semi-direction l) sd# xaxis-semi-dir) ->
      ⟨ OnLine' l (line'->x-intercept l l#x) ⟩
  line'->x-intercept-on-line' (p , sd) l#x =
    point-semi-direction->x-intercept-on-span p sd l#x

  line'->point-on-line' :
    (l : Line') -> (l#x : (line'-semi-direction l) sd# xaxis-semi-dir) -> Σ Point (fst ∘ OnLine' l)
  line'->point-on-line' l l#x =
    line'->x-intercept l l#x , line'->x-intercept-on-line' l l#x


  line'->x-intercept-full :
    (l : Line') ->
    isContr (
      semi-direction-distance' (line'-semi-direction l) xaxis-vector # 0# ->
      Σ[ p ∈ Point ] (⟨ OnLine' l p ⟩ × ⟨ OnLine' xaxis-line' p ⟩))
  line'->x-intercept-full (lp , sd) = point-semi-direction->x-intercept-full lp sd

  line->x-intercept-full :
    (l : Line) ->
    isContr (ConvergentLines l xaxis-line ->
             Σ[ p ∈ Point ] (⟨ OnLine l p ⟩ × ⟨ OnLine xaxis-line p ⟩))
  line->x-intercept-full = SetQuotientElim.liftContr _ _ line'->x-intercept-full



  point-direction->OnLine' :
    (p : Point) (d : Direction) -> (d#0 : semi-direction-distance d xaxis-vector # 0#) ->
    ⟨ OnLine' (p , [ d ]) (point-direction->x-intercept p d d#0) ⟩
  point-direction->OnLine' p d d#0 = point-direction->x-intercept-on-span p d d#0

  point-semi-direction->OnLine' :
    (p : Point) (sd : SemiDirection) -> (sd#0 : semi-direction-distance' sd xaxis-vector # 0#) ->
    ⟨ OnLine' (p , sd) (point-semi-direction->x-intercept p sd sd#0) ⟩
  point-semi-direction->OnLine' p sd sd#0 = point-semi-direction->x-intercept-on-span p sd sd#0
