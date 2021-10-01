{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.point-line-apartness where

open import apartness
open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import functions
open import cartesian-geometry
open import cartesian-geometry.line
open import cartesian-geometry.rotation
open import cartesian-geometry.semi-direction
open import cartesian-geometry.vector
open import order.instances.real
open import real
open import real.arithmetic.absolute-value
open import real.arithmetic.sqrt
open import real.heyting-field
open import ring.implementations.real
open import hlevel
open import relation
open import vector-space.finite
open import vector-space
open import order
open import subset
open import sigma
open import funext
open import set-quotient

private
  direction-basis : Direction -> Axis -> Vector
  direction-basis d = (rotate-vector (direction-diff xaxis-dir d)) ∘ axis-basis

  isBasis-direction-basis : (d : Direction) -> isBasis (direction-basis d)
  isBasis-direction-basis d =
    transform-basis (isLinearTransformation-rotate-vector r)
                    (isEquiv-rotate-vector r)
                    isBasis-axis-basis
    where
    r = (direction-diff xaxis-dir d)

  direction-basis-decomposition :
    (d : Direction) (v : Vector) (a : Axis) ->
    (basis-decomposition (isBasis-direction-basis d) v a) ==
    (vector-index (rotate-vector (direction-diff d xaxis-dir) v) a)
  direction-basis-decomposition d v a = cong (\r -> vector-index (rotate-vector r v) a) p
    where
    p : - (direction-diff xaxis-dir d) == (direction-diff d xaxis-dir)
    p = (minus-distrib-plus >=> +-right minus-double-inverse >=> +-commute)


  direction-basis-x-axis : (d : Direction) -> direction-basis d x-axis == ⟨ d ⟩
  direction-basis-x-axis d = cong fst p1
    where
    p1 : direction-shift xaxis-dir (direction-diff xaxis-dir d) == d
    p1 = direction-diff-step xaxis-dir d

  direction-signed-distance : (d : Direction) (v : Vector) -> ℝ
  direction-signed-distance d v =
    (basis-decomposition (isBasis-direction-basis d) v y-axis)

  direction-signed-distance-distrib-v+ :
    (d : Direction) (v1 v2 : Vector) ->
    (direction-signed-distance d (v1 v+ v2)) ==
    (direction-signed-distance d v1) + (direction-signed-distance d v2)
  direction-signed-distance-distrib-v+ d v1 v2 =
    (direction-basis-decomposition d (v1 v+ v2) y-axis) >=>
    cong (\v -> vector-index v y-axis) v-path >=>
    cong2 _+_ (sym (direction-basis-decomposition d v1 y-axis))
              (sym (direction-basis-decomposition d v2 y-axis))
    where
    v-path : (rotate-vector (direction-diff d xaxis-dir) (v1 v+ v2)) ==
             (rotate-vector (direction-diff d xaxis-dir) v1) v+
             (rotate-vector (direction-diff d xaxis-dir) v2)
    v-path = rotate-vector-preserves-+ (direction-diff d xaxis-dir) v1 v2




  semi-direction-distance : (d : Direction) (v : Vector) -> ℝ
  semi-direction-distance d v =
    absℝ (direction-signed-distance d v)


  semi-direction-distance-v- : (d : Direction) -> {v1 v2 : Vector} -> v1 == (v- v2) ->
    semi-direction-distance d v1 == semi-direction-distance d v2
  semi-direction-distance-v- d {v1} {v2} v1=-v2 =
    cong absℝ (dec1=-dec2 y-axis) >=> absℝ-- _
    where

    dec1 : Axis -> ℝ
    dec1 = (basis-decomposition (isBasis-direction-basis d) v1)

    dec2 : Axis -> ℝ
    dec2 = (basis-decomposition (isBasis-direction-basis d) v2)

    p : (rotate-vector (direction-diff d xaxis-dir) v1) ==
        (v- (rotate-vector (direction-diff d xaxis-dir) v2))
    p = cong (rotate-vector (direction-diff d xaxis-dir)) v1=-v2 >=>
        rotate-v- (direction-diff d xaxis-dir) v2

    dec1=-dec2 : (a : Axis) -> dec1 a == - (dec2 a)
    dec1=-dec2 a =
      (direction-basis-decomposition d v1 a >=>
       cong (\v -> vector-index v a) p >=>
       cong -_ (sym (direction-basis-decomposition d v2 a)))


  sym-semi-direction-distance :
    (d1 d2 : Direction) ->
    semi-direction-distance d1 ⟨ d2 ⟩ == semi-direction-distance d2 ⟨ d1 ⟩
  sym-semi-direction-distance d1 d2 =
    cong absℝ dec1=-dec2 >=> absℝ-- _
    where
    v1 = ⟨ d1 ⟩
    v2 = ⟨ d2 ⟩
    r1 = direction->rotation d1
    r2 = direction->rotation d2


    dec1 : Axis -> ℝ
    dec1 = basis-decomposition (isBasis-direction-basis d1) v2

    dec2 : Axis -> ℝ
    dec2 = basis-decomposition (isBasis-direction-basis d2) v1

    p2 : (rotate-direction (direction-diff d1 xaxis-dir) d2) ==
         (conjugate-direction (rotate-direction (direction-diff d2 xaxis-dir) d1))
    p2 =
      sym (rotate-direction-assoc (direction->rotation xaxis-dir) (r- r1) d2) >=>
      cong (direction-shift _) (rotation-ext refl) >=>
      rotate-direction-zero-rotation (rotate-direction (r- r1) d2) >=>
      cong (\r -> rotate-direction r d2) (r--direction->rotation d1) >=>
      rotate-direction-commute (conjugate-direction d1) d2 >=>
      cong (\r -> rotate-direction r (conjugate-direction d1))
        (sym (cong r-_ +-left-zero >=> minus-double-inverse)) >=>
      cong (direction-shift _) (cong r-_ (+-left (rotation-ext refl))) >=>
      sym (conjugate-distrib-rotate-direction (direction-diff d2 xaxis-dir) d1)

    p : (rotate-vector (direction-diff d1 xaxis-dir) v2) ==
        (conjugate-vector (rotate-vector (direction-diff d2 xaxis-dir) v1))
    p = cong ⟨_⟩ p2


    dec1=-dec2 : dec1 y-axis == - (dec2 y-axis)
    dec1=-dec2 =
      (direction-basis-decomposition d1 v2 y-axis >=>
       cong (\v -> vector-index v y-axis) p >=>
       cong -_ (sym (direction-basis-decomposition d2 v1 y-axis)))



  abstract
    semi-direction-distance0->0y :
      (d : Direction) (v : Vector) -> semi-direction-distance d v == 0# ->
      basis-decomposition (isBasis-direction-basis d) v y-axis == 0#
    semi-direction-distance0->0y d v dis0 = absℝ-zero dis0

  semi-direction-distance0->direction-span :
    (d : Direction) (v : Vector) -> semi-direction-distance d v == 0# -> direction-span' d v
  semi-direction-distance0->direction-span d@(dv , dp) v dis0 =
    basis-decomposition b v x-axis ,
    v*-right x-path >=>
    sym v+-right-zero >=>
    v+-right (sym v*-left-zero >=> v*-left (sym y0)) >=>
    sym (axis-merge _) >=>
    basis-decomposition-path b
    where
    b = isBasis-direction-basis d

    y0 = semi-direction-distance0->0y d v dis0

    x-path : dv == rotate-vector (direction-diff xaxis-dir d) xaxis-vector
    x-path = sym (direction-basis-x-axis d)


  direction-span->semi-direction-distance0 :
    (d : Direction) (v : Vector) -> direction-span' d v -> semi-direction-distance d v == 0#
  direction-span->semi-direction-distance0 d@(dv , dp) v (k , kdv=v) = ans
    where
    b' = direction-basis d
    b = isBasis-direction-basis d
    c = (basis-decomposition b v)

    x-path : b' x-axis == dv
    x-path = (direction-basis-x-axis d)

    kx-path : k v* (b' x-axis) == v
    kx-path = v*-right x-path >=> kdv=v

    c2 : Axis -> ℝ
    c2 x-axis = k
    c2 y-axis = 0#

    scaled-sum-path : scaled-vector-sum c2 b' == v
    scaled-sum-path = axis-merge _ >=> v+-right v*-left-zero >=> v+-right-zero >=> kx-path

    ans2 : c y-axis == 0#
    ans2 = cong (\f -> f y-axis) (sym (basis-decomposition-unique b scaled-sum-path))

    ans : absℝ (c y-axis) == 0#
    ans = cong absℝ ans2 >=> absℝ-NonNeg-idem 0ℝ (refl-≤ {_} {_} {_} {0ℝ})


  isProp-semi-direction-distance0 : (d : Direction) (v : Vector) ->
    isProp (semi-direction-distance d v == 0#)
  isProp-semi-direction-distance0 d v = isSet-ℝ _ _

  semi-direction-distance0-Subtype : (d : Direction) -> Subtype Vector ℓ-one
  semi-direction-distance0-Subtype d v =
    (semi-direction-distance d v == 0#) , isProp-semi-direction-distance0 d v

  direction-span=semi-direction-distance0 : (d : Direction) ->
    direction-span d == semi-direction-distance0-Subtype d
  direction-span=semi-direction-distance0 d =
    same-Subtype (\{v} -> direction-span->semi-direction-distance0 d v)
                 (\{v} -> semi-direction-distance0->direction-span d v)

  direction-span'-comp : Direction -> Pred Vector ℓ-one
  direction-span'-comp d v = semi-direction-distance d v # 0#

  direction-span'-comp-tight : (d : Direction) (v : Vector) ->
                                ¬ (direction-span'-comp d v) -> direction-span' d v
  direction-span'-comp-tight d v ¬dis#0 =
    transport (sym (cong (\f -> (fst (f v))) (direction-span=semi-direction-distance0 d)))
              (tight-# ¬dis#0)

  direction-span-comp : Direction -> Subtype Vector ℓ-one
  direction-span-comp d v = direction-span'-comp d v , isProp-#


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

  0≤semi-direction-distance' : (sd : SemiDirection) -> (v : Vector) -> 0# ≤ semi-direction-distance' sd v
  0≤semi-direction-distance' sd v =
    SemiDirectionElim.elimProp
      (\sd -> isProp-≤ _ (semi-direction-distance' sd v))
      (\d -> (absℝ-≮0 _)) sd


  semi-direction-distance'-v- : {v1 v2 : Vector} (sd : SemiDirection) -> v1 == (v- v2) ->
    semi-direction-distance' sd v1 == semi-direction-distance' sd v2
  semi-direction-distance'-v- {v1} {v2} =
    SemiDirectionElim.elimProp
      (\_ -> (isPropΠ (\_ -> isSet-ℝ _ _)))
      (\d -> semi-direction-distance-v- d {v1} {v2})

  -- same-semi-direction-span-comp : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
  --                                  (direction-span-comp d1) == (direction-span-comp d2)
  -- same-semi-direction-span-comp d1 d2 same-semi =
  --   same-Subtype (\{v} -> handle same-semi {v})
  --                (\{v} -> handle (sym-SameSemiDirection same-semi) {v})
  --   where
  --   handle : {d1 d2 : Direction} -> SameSemiDirection d1 d2 -> {v : Vector} ->
  --            (direction-span'-comp d1 v) -> (direction-span'-comp d2 v)
  --   handle {d1} {d2} same {v} dis#0 =
  --     subst (\ sd -> semi-direction-distance' sd v # 0#) (eq/ d1 d2 same) dis#0

  -- semi-direction-span-comp : SemiDirection -> Subtype Vector ℓ-one
  -- semi-direction-span-comp sd v = semi-direction-distance' sd v # 0# , isProp-#

  semi-direction-distance'0-Subtype : (sd : SemiDirection) -> Subtype Vector ℓ-one
  semi-direction-distance'0-Subtype sd v =
    (semi-direction-distance' sd v == 0#) , isSet-ℝ _ _


  semi-direction-span=semi-direction-distance'0 : (sd : SemiDirection) ->
    semi-direction-span sd == semi-direction-distance'0-Subtype sd
  semi-direction-span=semi-direction-distance'0 sd =
    SemiDirectionElim.elimProp
      (\sd -> isSet-Subtype (semi-direction-span sd) (semi-direction-distance'0-Subtype sd))
      (\d -> direction-span=semi-direction-distance0 d >=>
             funExt (\v -> ΣProp-path isProp-isProp refl))
      sd


  semi-direction-span->semi-direction-distance'0 :
    (sd : SemiDirection) (v : Vector) ->
    ⟨ semi-direction-span sd v ⟩ ->
    semi-direction-distance' sd v == 0#
  semi-direction-span->semi-direction-distance'0 =
    SemiDirectionElim.elimProp (\_ -> (isPropΠ2 \_ _ -> isSet-ℝ _ _) )
      direction-span->semi-direction-distance0

  semi-direction-distance-cancel0 : (d : Direction) (v1 v2 : Vector) ->
    semi-direction-distance d v1 == 0# ->
    semi-direction-distance d (v1 v+ v2) == semi-direction-distance d v2
  semi-direction-distance-cancel0 d v1 v2 p =
    cong absℝ (direction-signed-distance-distrib-v+ d v1 v2 >=>
               +-left (absℝ-zero p) >=> +-left-zero)

  semi-direction-distance'-cancel0 : (sd : SemiDirection) (v1 v2 : Vector) ->
    semi-direction-distance' sd v1 == 0# ->
    semi-direction-distance' sd (v1 v+ v2) == semi-direction-distance' sd v2
  semi-direction-distance'-cancel0 sd v1 v2 =
    SemiDirectionElim.elimProp
      (\sd -> (isPropΠ \(_ : semi-direction-distance' sd v1 == 0#) ->
                         isSet-ℝ (semi-direction-distance' sd (v1 v+ v2))
                                 (semi-direction-distance' sd v2)))
      (\d -> semi-direction-distance-cancel0 d v1 v2) sd

  point-line'-distance : Point -> Line' -> ℝ
  point-line'-distance p (lp , sd) = semi-direction-distance' sd (P-diff lp p)

  point-line'-distance-SameLine' :
    (p : Point) (l1 l2 : Line') -> SameLine' l1 l2 ->
    point-line'-distance p l1 == point-line'-distance p l2
  point-line'-distance-SameLine' p (p1 , sd1) (p2 , sd2) (p2∈l1 , p1∈l2 , sd1=sd2) = ans
    where
    sdd-1 = semi-direction-distance' sd1 (P-diff p1 p)
    sdd-2 = semi-direction-distance' sd2 (P-diff p2 p)
    sdd-2' = semi-direction-distance' sd1 (P-diff p2 p)
    sdd-diff = semi-direction-distance' sd1 ((P-diff p2 p1) v+ (P-diff p1 p))

    p2∈l1' : ⟨ semi-direction-span sd1 (P-diff p2 p1) ⟩
    p2∈l1' = subst (\sd -> ⟨ semi-direction-span sd (P-diff p2 p1) ⟩) (sym sd1=sd2) p1∈l2

    +-path : sdd-1 == sdd-diff
    +-path = sym (semi-direction-distance'-cancel0
                   sd1 (P-diff p2 p1) (P-diff p1 p)
                   (semi-direction-span->semi-direction-distance'0 sd1 (P-diff p2 p1) p2∈l1'))

    ans : sdd-1 == sdd-2
    ans =
      +-path >=>
      cong (semi-direction-distance' sd1) (P-diff-trans p2 p1 p) >=>
      cong (\sd -> semi-direction-distance' sd (P-diff p2 p)) sd1=sd2


  point-line-distance : Point -> Line -> ℝ
  point-line-distance p =
    SetQuotientElim.rec Line' SameLine' isSet-ℝ
      (\ l -> point-line'-distance p l)
      (\ l1 l2 sl -> point-line'-distance-SameLine' p l1 l2 sl)

  0≤point-line-distance : (p : Point) -> (l : Line) -> 0# ≤ point-line-distance p l
  0≤point-line-distance p =
    SetQuotientElim.elimProp Line' SameLine' (\l -> isProp-≤ _ _)
      (\(lp , sd) -> 0≤semi-direction-distance' sd (P-diff lp p))

  point-line-distance0-Subtype : (l : Line) -> Subtype Point ℓ-one
  point-line-distance0-Subtype l p =
    (point-line-distance p l == 0#) , isSet-ℝ _ _


  OnLine=point-line-distance0 : (l : Line) ->
    OnLine l == point-line-distance0-Subtype l
  OnLine=point-line-distance0 =
    SetQuotientElim.elimProp Line' SameLine' (\l -> isSet-Subtype _ _)
      (\l -> funExt (f l))
    where
    f : (l : Line') (p : Point) -> OnLine' l p == point-line-distance0-Subtype [ l ] p
    f (lp , sd) p =
      cong (\s -> s (P-diff lp p)) (semi-direction-span=semi-direction-distance'0 sd) >=>
      ΣProp-path isProp-isProp refl



OffLine : Line -> Subtype Point ℓ-one
OffLine l p = 0# < point-line-distance p l , isProp-< _ _

¬OffLine->OnLine : (l : Line) (p : Point) -> ¬ ⟨ OffLine l p ⟩ -> ⟨ OnLine l p ⟩
¬OffLine->OnLine l p 0≮dis = subst (\s -> fst (s p)) (sym (OnLine=point-line-distance0 l)) dis=0
  where
  dis=0 = sym (strengthen-≤-≮ (0≤point-line-distance p l) 0≮dis)
