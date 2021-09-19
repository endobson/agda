{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.rotation where

open import apartness
open import base
open import cartesian-geometry.vector
open import cubical using (isEquiv)
open import direct-product
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import order
open import order.instances.real
open import real
open import real.arithmetic.absolute-value
open import real.arithmetic.sqrt
open import real.arithmetic.sqrt.base
open import real.heyting-field
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import sigma
open import solver
open import subset
open import vector-space
open import vector-space.finite

record Rotation : Type₁ where
  constructor rotation
  field
    dir : Direction

rotation-ext : {r1 r2 : Rotation} -> (Rotation.dir r1) == (Rotation.dir r2) -> r1 == r2
rotation-ext p i = record { dir = p i }



zero-rotation : Direction
zero-rotation = xaxis-dir

zero-rotation=xaxis-dir : zero-rotation == xaxis-dir
zero-rotation=xaxis-dir = refl

rotate : Direction -> Vector -> Vector
rotate (d , _) v = direct-product-cons f
  where
  f : Axis -> ℝ
  f x-axis = (direct-product-index d x-axis) * (direct-product-index v x-axis) +
             (- ((direct-product-index d y-axis) * (direct-product-index v y-axis)))
  f y-axis = (direct-product-index d x-axis) * (direct-product-index v y-axis) +
             (direct-product-index d y-axis) * (direct-product-index v x-axis)

rotate-preserves-vector-length² :
  (d : Direction) (v : Vector) -> vector-length² (rotate d v) == vector-length² v
rotate-preserves-vector-length² (d , vl-d=1) v = ans
  where
  dx = direct-product-index d x-axis
  dy = direct-product-index d y-axis
  vx = direct-product-index v x-axis
  vy = direct-product-index v y-axis

  reorder : (dx * vx + (- (dy * vy))) * (dx * vx + (- (dy * vy))) +
            (dx * vy + dy * vx) * (dx * vy + dy * vx) ==
            (dx * dx + dy * dy) * (vx * vx + vy * vy)
  reorder = RingSolver.solve ℝRing 4
            (\dx dy vx vy ->
              (dx ⊗ vx ⊕ (⊖ (dy ⊗ vy))) ⊗ (dx ⊗ vx ⊕ (⊖ (dy ⊗ vy))) ⊕
              (dx ⊗ vy ⊕ dy ⊗ vx) ⊗ (dx ⊗ vy ⊕ dy ⊗ vx),
              (dx ⊗ dx ⊕ dy ⊗ dy) ⊗ (vx ⊗ vx ⊕ vy ⊗ vy))
            refl dx dy vx vy

  ans : (dx * vx + (- (dy * vy))) * (dx * vx + (- (dy * vy))) +
        (dx * vy + dy * vx) * (dx * vy + dy * vx) ==
        (vx * vx) + (vy * vy)
  ans = reorder >=> *-left (eqInv (isUnitVector'-equiv d) vl-d=1) >=> *-left-one

rotate-preserves-vector-length :
  (d : Direction) (v : Vector) -> vector-length (rotate d v) == vector-length v
rotate-preserves-vector-length d v =
  cong2-dep sqrtℝ p (isProp->PathP (\i -> isProp-≤ 0ℝ (p i)) _ _)
  where
  p = rotate-preserves-vector-length² d v

rotate-direction : Direction -> Direction -> Direction
rotate-direction d (v , vl=1) = rotate d v , vl=1'
  where
  abstract
    vl=1' = rotate-preserves-vector-length d v >=> vl=1

abstract
  rotate-d- : (d : Direction) (v : Vector) -> (rotate (d- d) v) == v- (rotate d v)
  rotate-d- d@(dv , _) v = vector-ext f
    where
    dx = vector-index dv x-axis
    dy = vector-index dv y-axis
    vx = vector-index v x-axis
    vy = vector-index v y-axis

    f : (a : Axis) -> (vector-index (rotate (d- d) v) a) == (vector-index (v- (rotate d v)) a)
    f x-axis = ans
      where
      ans : (- dx) * vx + (- ((- dy) * vy)) == - (dx * vx + (- (dy * vy)))
      ans = +-cong minus-extract-left (cong -_ minus-extract-left) >=>
            sym minus-distrib-plus
    f y-axis = ans
      where
      ans : (- dx) * vy + (- dy) * vx == - (dx * vy + dy * vx)
      ans = +-cong minus-extract-left minus-extract-left >=> sym minus-distrib-plus

  rotate-v- : (d : Direction) (v : Vector) -> (rotate d (v- v)) == v- (rotate d v)
  rotate-v- d@(dv , _) v = vector-ext f
    where
    dx = vector-index dv x-axis
    dy = vector-index dv y-axis
    vx = vector-index v x-axis
    vy = vector-index v y-axis

    f : (a : Axis) -> (vector-index (rotate d (v- v)) a) == (vector-index (v- (rotate d v)) a)
    f x-axis = ans
      where
      ans : dx * (- vx) + (- (dy * (- vy))) == - (dx * vx + (- (dy * vy)))
      ans = +-cong minus-extract-right (cong -_ minus-extract-right) >=>
            sym minus-distrib-plus
    f y-axis = ans
      where
      ans : dx * (- vy) + dy * (- vx) == - (dx * vy + dy * vx)
      ans = +-cong minus-extract-right minus-extract-right >=> sym minus-distrib-plus


  rotate-zero-rotation : (v : Vector) -> (rotate zero-rotation v) == v
  rotate-zero-rotation v = \i -> direct-product-cons (\a -> (f a i))
    where
    f : (a : Axis) -> (direct-product-index (rotate zero-rotation v) a) ==
                      (direct-product-index v a)
    f x-axis = +-cong *-left-one (cong -_ *-left-zero >=> minus-zero) >=> +-right-zero
    f y-axis = +-cong *-left-one *-left-zero >=> +-right-zero

  rotate-direction-zero-rotation : (d : Direction) -> (rotate-direction zero-rotation d) == d
  rotate-direction-zero-rotation (v , _) =
    ΣProp-path (\{v} -> isProp-isUnitVector v) (rotate-zero-rotation v)

  rotate-direction-commute : (d1 d2 : Direction) -> rotate-direction d1 d2 == rotate-direction d2 d1
  rotate-direction-commute d1@(v1 , _) d2@(v2 , _) =
    ΣProp-path (\{v} -> isProp-isUnitVector v) (\i -> direct-product-cons (\a -> f a i))
    where
    f : (a : Axis) -> direct-product-index (rotate d1 v2) a ==
                      direct-product-index (rotate d2 v1) a
    f x-axis = +-cong *-commute (cong -_ *-commute)
    f y-axis = +-commute >=> +-cong *-commute *-commute

  rotate-direction-conjugate :
    (d : Direction) -> (rotate-direction d (conjugate-direction d)) == zero-rotation
  rotate-direction-conjugate d@(v , p) =
    ΣProp-path (\{v} -> isProp-isUnitVector v) (\i -> direct-product-cons (\a -> f a i))
    where
    f : (a : Axis) -> (direct-product-index (rotate d (conjugate-vector v)) a) ==
                      (direct-product-index (fst xaxis-dir) a)
    f x-axis = +-right (cong -_ minus-extract-right >=> minus-double-inverse) >=>
               (eqInv (isUnitVector'-equiv v) p)
    f y-axis = +-cong minus-extract-right *-commute >=> +-commute >=> +-inverse


  conjugate-distrib-rotate :
    (d : Direction) (v : Vector) ->
    (conjugate-vector (rotate d v)) == (rotate (conjugate-direction d) (conjugate-vector v))
  conjugate-distrib-rotate d@(dv , _) v = (vector-ext f)
    where
    f : (a : Axis) -> (vector-index (conjugate-vector (rotate d v)) a) ==
                      (vector-index (rotate (conjugate-direction d) (conjugate-vector v)) a)
    f x-axis = +-right (cong -_ (sym minus-extract-both))
    f y-axis = minus-distrib-plus >=> +-cong (sym minus-extract-right) (sym minus-extract-left)


  conjugate-distrib-rotate-direction :
    (d1 d2 : Direction)  ->
    (conjugate-direction (rotate-direction d1 d2)) ==
    (rotate-direction (conjugate-direction d1) (conjugate-direction d2))
  conjugate-distrib-rotate-direction d1 d2 = direction-ext (conjugate-distrib-rotate d1 ⟨ d2 ⟩)



  rotate-assoc : (d1 d2 : Direction) (v : Vector) ->
                 (rotate d1 (rotate d2 v)) == (rotate (rotate-direction d1 d2) v)
  rotate-assoc d1@(dv1 , _) d2@(dv2 , _) v = \i -> direct-product-cons (\a -> (f a i))
    where
    d1x = direct-product-index dv1 x-axis
    d1y = direct-product-index dv1 y-axis
    d2x = direct-product-index dv2 x-axis
    d2y = direct-product-index dv2 y-axis
    vx = direct-product-index v x-axis
    vy = direct-product-index v y-axis

    f : (a : Axis) -> (direct-product-index (rotate d1 (rotate d2 v)) a) ==
                      (direct-product-index (rotate (rotate-direction d1 d2) v) a)
    f x-axis =
      RingSolver.solve ℝRing 6
        (\d1x d1y d2x d2y vx vy ->
          d1x ⊗ (d2x ⊗ vx ⊕ (⊖ (d2y ⊗ vy))) ⊕ (⊖ (d1y ⊗ (d2x ⊗ vy ⊕ (d2y ⊗ vx)))) ,
          ((d1x ⊗ d2x ⊕ (⊖ (d1y ⊗ d2y))) ⊗ vx) ⊕ (⊖ ((d1x ⊗ d2y ⊕ d1y ⊗ d2x) ⊗ vy)))
        refl d1x d1y d2x d2y vx vy
    f y-axis =
      RingSolver.solve ℝRing 6
        (\d1x d1y d2x d2y vx vy ->
          d1x ⊗ (d2x ⊗ vy ⊕ d2y ⊗ vx) ⊕ d1y ⊗ (d2x ⊗ vx ⊕ (⊖ (d2y ⊗ vy))) ,
          ((d1x ⊗ d2x ⊕ (⊖ (d1y ⊗ d2y))) ⊗ vy) ⊕ ((d1x ⊗ d2y ⊕ d1y ⊗ d2x) ⊗ vx))
        refl d1x d1y d2x d2y vx vy

isEquiv-rotate : (d : Direction) -> isEquiv (rotate d)
isEquiv-rotate d = snd (isoToEquiv i)
  where
  open Iso
  i : Iso Vector Vector
  i .fun = rotate d
  i .inv = rotate (conjugate-direction d)
  i .rightInv v = rotate-assoc d (conjugate-direction d) v >=>
                  cong (\d -> rotate d v) (rotate-direction-conjugate d) >=>
                  rotate-zero-rotation v
  i .leftInv v = rotate-assoc (conjugate-direction d) d v >=>
                 cong (\d -> rotate d v) ((rotate-direction-commute (conjugate-direction d) d) >=>
                                          rotate-direction-conjugate d) >=>
                 rotate-zero-rotation v

rotate-preserves-+ :
  (d : Direction) (v1 v2 : Vector) ->
  rotate d (v1 v+ v2) == rotate d v1 v+ rotate d v2
rotate-preserves-+ d@(dv , _) v1 v2 = \i -> direct-product-cons (\a -> (f a i))
  where
  dx = direct-product-index dv x-axis
  dy = direct-product-index dv y-axis
  v1x = direct-product-index v1 x-axis
  v1y = direct-product-index v1 y-axis
  v2x = direct-product-index v2 x-axis
  v2y = direct-product-index v2 y-axis

  f : (a : Axis) -> (direct-product-index (rotate d (v1 v+ v2)) a) ==
                    (direct-product-index (rotate d v1 v+ rotate d v2) a)
  f x-axis = RingSolver.solve ℝRing 6
             (\dx dy v1x v1y v2x v2y ->
               dx ⊗ (v1x ⊕ v2x) ⊕ (⊖ (dy ⊗ (v1y ⊕ v2y))) ,
               (dx ⊗ v1x ⊕ (⊖ (dy ⊗ v1y))) ⊕ (dx ⊗ v2x ⊕ (⊖ (dy ⊗ v2y))))
             refl dx dy v1x v1y v2x v2y
  f y-axis = RingSolver.solve ℝRing 6
             (\dx dy v1x v1y v2x v2y ->
               dx ⊗ (v1y ⊕ v2y) ⊕ dy ⊗ (v1x ⊕ v2x) ,
               (dx ⊗ v1y ⊕ dy ⊗ v1x) ⊕ (dx ⊗ v2y ⊕ dy ⊗ v2x))
             refl dx dy v1x v1y v2x v2y

rotate-preserves-* :
  (d : Direction) (k : ℝ) (v : Vector) ->
  rotate d (k v* v) == k v* (rotate d v)
rotate-preserves-* d@(dv , _) k v = \i -> direct-product-cons (\a -> (f a i))
  where
  dx = direct-product-index dv x-axis
  dy = direct-product-index dv y-axis
  vx = direct-product-index v x-axis
  vy = direct-product-index v y-axis

  f : (a : Axis) -> (direct-product-index (rotate d (k v* v)) a) ==
                    (direct-product-index (k v* (rotate d v)) a)
  f x-axis = RingSolver.solve ℝRing 5
             (\dx dy k vx vy ->
               (dx ⊗ (k ⊗ vx) ⊕ (⊖ (dy ⊗ (k ⊗ vy))) ,
                k ⊗ (dx ⊗ vx ⊕ (⊖ (dy ⊗ vy)))))
             refl dx dy k vx vy
  f y-axis = RingSolver.solve ℝRing 5
             (\dx dy k vx vy ->
               (dx ⊗ (k ⊗ vy) ⊕ dy ⊗ (k ⊗ vx) ,
                k ⊗ (dx ⊗ vy ⊕ dy ⊗ vx)))
             refl dx dy k vx vy

isLinearTransformation-rotate : (d : Direction) -> isLinearTransformation (rotate d)
isLinearTransformation-rotate d =
  is-linear-transformation (rotate-preserves-+ d) (rotate-preserves-* d)



_r+_ : Rotation -> Rotation -> Rotation
_r+_ (rotation d1) (rotation d2) = rotation (rotate-direction d1 d2)






-- Rotated basis and semi-direction-distance
-- TODO find it a better home

rotated-basis : Direction -> Axis -> Vector
rotated-basis d = (rotate d) ∘ axis-basis

isBasis-rotated-basis : (d : Direction) -> isBasis (rotated-basis d)
isBasis-rotated-basis d =
  transform-basis (isLinearTransformation-rotate d)
                  (isEquiv-rotate d)
                  isBasis-axis-basis

rotated-basis-x-axis : (d : Direction) -> rotated-basis d x-axis == ⟨ d ⟩
rotated-basis-x-axis d = cong fst p4
  where
  p1 : rotate-direction d xaxis-dir == rotate-direction xaxis-dir d
  p1 = rotate-direction-commute d xaxis-dir

  p2 : rotate-direction zero-rotation d == d
  p2 = rotate-direction-zero-rotation d

  p3 : rotate-direction xaxis-dir d == rotate-direction zero-rotation d
  p3 = cong (\d2 -> rotate-direction d2 d) (sym zero-rotation=xaxis-dir)

  p4 = p1 >=> p3 >=> p2


semi-direction-distance : (d : Direction) (v : Vector) -> ℝ
semi-direction-distance d v =
  absℝ (basis-decomposition (isBasis-rotated-basis d) v y-axis)


semi-direction-distance-v- : (d : Direction) -> {v1 v2 : Vector} -> v1 == (v- v2) ->
  semi-direction-distance d v1 == semi-direction-distance d v2
semi-direction-distance-v- d {v1} {v2} v1=-v2 =
  cong absℝ (dec1=-dec2 y-axis) >=> absℝ-- _
  where

  dec1 : Axis -> ℝ
  dec1 = (basis-decomposition (isBasis-rotated-basis d) v1)

  dec2 : Axis -> ℝ
  dec2 = (basis-decomposition (isBasis-rotated-basis d) v2)

  dec1=-dec2 : (a : Axis) -> dec1 a == - (dec2 a)
  dec1=-dec2 a =
    cong (\d -> vector-index d a)
      (cong (rotate (conjugate-direction d)) v1=-v2 >=>
       rotate-v- (conjugate-direction d) v2)


sym-semi-direction-distance :
  (d1 d2 : Direction) ->
  semi-direction-distance d1 ⟨ d2 ⟩ == semi-direction-distance d2 ⟨ d1 ⟩
sym-semi-direction-distance d1 d2 =
  cong absℝ (cong (\d -> vector-index ⟨ d ⟩ y-axis) path) >=>
  absℝ-- _
  where
  c = conjugate-direction
  r = rotate-direction

  path : (r (c d1) d2) ==
         (c (r (c d2) d1))
  path = sym (conjugate-distrib-rotate-direction (c d2) d1 >=>
              rotate-direction-commute (c (c d2)) (c d1) >=>
              cong (r (c d1)) (conjugate-direction-double-inverse d2))


-- semi-direction-distance-comparison' :
--   (d1 d2 d3 : Direction) ->
--   semi-direction-distance d1 ⟨ d3 ⟩ # semi-direction-distance d1 ⟨ d2 ⟩ ->
--   semi-direction-distance d2 ⟨ d3 ⟩ # 0#
-- semi-direction-distance-comparison' d1@(v1 , p1) d2@(v2 , p2) d3@(v3 , p3) dis# = ?
--   where
--   check : absℝ (basis-decomposition (isBasis-rotated-basis d1) v3 y-axis) #
--           absℝ (basis-decomposition (isBasis-rotated-basis d1) v2 y-axis)
--   check = ?


abstract
  semi-direction-distance0->0y :
    (d : Direction) (v : Vector) -> semi-direction-distance d v == 0# ->
    basis-decomposition (isBasis-rotated-basis d) v y-axis == 0#
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
  b = isBasis-rotated-basis d

  y0 = semi-direction-distance0->0y d v dis0

  x-path : dv == rotate d xaxis-vector
  x-path = sym (rotated-basis-x-axis d)


direction-span->semi-direction-distance0 :
  (d : Direction) (v : Vector) -> direction-span' d v -> semi-direction-distance d v == 0#
direction-span->semi-direction-distance0 d@(dv , dp) v (k , kdv=v) = ans
  where
  b' = rotated-basis d
  b = isBasis-rotated-basis d
  c = (basis-decomposition b v)

  x-path : b' x-axis == dv
  x-path = (rotated-basis-x-axis d)

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
