{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.rotation where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry.vector
open import cubical using (isEquiv ; I)
open import commutative-monoid
open import direct-product
open import equality
open import equivalence
open import functions
open import group
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import isomorphism
open import monoid
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
open import sum
open import truncation
open import vector-space
open import vector-space.finite


private
  raw-rotate : Vector -> Vector -> Vector
  raw-rotate r v = direct-product-cons f
    where
    f : Axis -> ℝ
    f x-axis = (direct-product-index r x-axis) * (direct-product-index v x-axis) +
               (- ((direct-product-index r y-axis) * (direct-product-index v y-axis)))
    f y-axis = (direct-product-index r x-axis) * (direct-product-index v y-axis) +
               (direct-product-index r y-axis) * (direct-product-index v x-axis)

  raw-rotate-vector-length² :
    (r : Vector) (v : Vector) ->
    vector-length² (raw-rotate r v) == (vector-length² r) * (vector-length² v)
  raw-rotate-vector-length² r v = reorder
    where
    rx = direct-product-index r x-axis
    ry = direct-product-index r y-axis
    vx = direct-product-index v x-axis
    vy = direct-product-index v y-axis

    reorder : (rx * vx + (- (ry * vy))) * (rx * vx + (- (ry * vy))) +
              (rx * vy + ry * vx) * (rx * vy + ry * vx) ==
              (rx * rx + ry * ry) * (vx * vx + vy * vy)
    reorder = RingSolver.solve ℝRing 4
              (\rx ry vx vy ->
                (rx ⊗ vx ⊕ (⊖ (ry ⊗ vy))) ⊗ (rx ⊗ vx ⊕ (⊖ (ry ⊗ vy))) ⊕
                (rx ⊗ vy ⊕ ry ⊗ vx) ⊗ (rx ⊗ vy ⊕ ry ⊗ vx),
                (rx ⊗ rx ⊕ ry ⊗ ry) ⊗ (vx ⊗ vx ⊕ vy ⊗ vy))
              refl rx ry vx vy

  raw-rotate-commute : (v1 v2 : Vector) -> raw-rotate v1 v2 == raw-rotate v2 v1
  raw-rotate-commute v1 v2 = vector-ext f
    where
    f : (a : Axis) -> vector-index (raw-rotate v1 v2) a ==
                      vector-index (raw-rotate v2 v1) a
    f x-axis = +-cong *-commute (cong -_ *-commute)
    f y-axis = +-commute >=> +-cong *-commute *-commute



record Rotation : Type₁ where
  no-eta-equality
  constructor rotation
  field
    dir : Direction

rotation-ext : {r1 r2 : Rotation} -> (Rotation.dir r1) == (Rotation.dir r2) -> r1 == r2
rotation-ext {r1@(rotation d1)} {r2@(rotation d2)} p = a.path
  where
  module a where
    abstract
      path : r1 == r2
      path = \i -> record { dir = p i }

isSet-Rotation : isSet Rotation
isSet-Rotation =
  isSet-Retract Rotation.dir rotation (\_ -> rotation-ext refl) isSet-Direction


zero-rotation : Rotation
zero-rotation = rotation xaxis-dir

half-rotation : Rotation
half-rotation = rotation (d- xaxis-dir)


rotate : Rotation -> Vector -> Vector
rotate (rotation (d , _)) v = raw-rotate d v

rotate-preserves-vector-length² :
  (r : Rotation) (v : Vector) -> vector-length² (rotate r v) == vector-length² v
rotate-preserves-vector-length² (rotation (dv , vl-d=1)) v =
  raw-rotate-vector-length² dv v >=> *-left (eqInv (isUnitVector'-equiv dv) vl-d=1) >=> *-left-one

rotate-preserves-vector-length :
  (r : Rotation) (v : Vector) -> vector-length (rotate r v) == vector-length v
rotate-preserves-vector-length r v =
  cong2-dep sqrtℝ p (isProp->PathP (\i -> isProp-≤ 0ℝ (p i)) _ _)
  where
  p = rotate-preserves-vector-length² r v

rotate-direction : Rotation -> Direction -> Direction
rotate-direction r (v , vl=1) = rotate r v , a.vl=1'
  where
  module a where
    abstract
      vl=1' : vector-length (rotate r v) == 1#
      vl=1' = rotate-preserves-vector-length r v >=> vl=1



_r+_ : Rotation -> Rotation -> Rotation
_r+_ r (rotation d) = rotation (rotate-direction r d)

r-_ : Rotation -> Rotation
r-_ (rotation d) = rotation (conjugate-direction d)

add-half-rotation : Rotation -> Rotation
add-half-rotation (rotation d) = (rotation (d- d))

direction-diff : Direction -> Direction -> Rotation
direction-diff d1 d2 = rotation d2 r+ (r- (rotation d1))

direction-shift : Direction -> Rotation -> Direction
direction-shift d r = rotate-direction r d

abstract
  rotate-zero-rotation : (v : Vector) -> (rotate zero-rotation v) == v
  rotate-zero-rotation v = \i -> direct-product-cons (\a -> (f a i))
    where
    f : (a : Axis) -> (direct-product-index (rotate zero-rotation v) a) ==
                      (direct-product-index v a)
    f x-axis = +-cong *-left-one (cong -_ *-left-zero >=> minus-zero) >=> +-right-zero
    f y-axis = +-cong *-left-one *-left-zero >=> +-right-zero

  r+-commute : (r1 r2 : Rotation) -> r1 r+ r2 == r2 r+ r1
  r+-commute (rotation (v1 , _)) (rotation (v2 , _)) =
    rotation-ext (direction-ext (raw-rotate-commute v1 v2))


  r+-left-zero : (r : Rotation) -> (zero-rotation r+ r) == r
  r+-left-zero (rotation (v , _)) = rotation-ext (direction-ext (rotate-zero-rotation v))

  r+-right-zero : (r : Rotation) -> (r r+ zero-rotation) == r
  r+-right-zero r = r+-commute r zero-rotation >=> r+-left-zero r


  rotate-assoc : (r1 r2 : Rotation) (v : Vector) ->
                 (rotate r1 (rotate r2 v)) == (rotate (r1 r+ r2) v)
  rotate-assoc r1@(rotation (dv1 , _)) r2@(rotation (dv2 , _)) v = vector-ext f
    where
    d1x = direct-product-index dv1 x-axis
    d1y = direct-product-index dv1 y-axis
    d2x = direct-product-index dv2 x-axis
    d2y = direct-product-index dv2 y-axis
    vx = direct-product-index v x-axis
    vy = direct-product-index v y-axis

    f : (a : Axis) -> (direct-product-index (rotate r1 (rotate r2 v)) a) ==
                      (direct-product-index (rotate (r1 r+ r2) v) a)
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

  rotate-direction-assoc :
    (r1 r2 : Rotation) (d : Direction) ->
    (rotate-direction r1 (rotate-direction r2 d)) == (rotate-direction (r1 r+ r2) d)
  rotate-direction-assoc r1 r2 d = direction-ext (rotate-assoc r1 r2 ⟨ d ⟩)

  r+-assoc : (r1 r2 r3 : Rotation) -> (r1 r+ r2) r+ r3 == r1 r+ (r2 r+ r3)
  r+-assoc r1 r2 r3@(rotation d3) =
    rotation-ext (sym (rotate-direction-assoc r1 r2 d3))


  r+-inverse : (r : Rotation) -> (r r+ (r- r)) == zero-rotation
  r+-inverse (rotation (v , p)) = rotation-ext (direction-ext (vector-ext f))
    where
    f : (a : Axis) -> (vector-index (raw-rotate v (conjugate-vector v)) a) ==
                      (vector-index xaxis-vector a)
    f x-axis = +-right (cong -_ minus-extract-right >=> minus-double-inverse) >=>
               (eqInv (isUnitVector'-equiv v) p)
    f y-axis = +-cong minus-extract-right *-commute >=> +-commute >=> +-inverse

  r--double-inverse : (r : Rotation) -> (r- (r- r)) == r
  r--double-inverse (rotation d) =
    rotation-ext (conjugate-direction-double-inverse d)


Monoid-Rotation : Monoid Rotation
Monoid-Rotation = record
  { ε = zero-rotation
  ; _∙_ = _r+_
  ; ∙-assoc = \{r1} {r2} {r3} -> r+-assoc r1 r2 r3
  ; ∙-left-ε = \{r} -> r+-left-zero r
  ; ∙-right-ε = \{r} -> r+-right-zero r
  }

CommMonoid-Rotation : CommMonoid Rotation
CommMonoid-Rotation = record
  { monoid = Monoid-Rotation
  ; ∙-commute = \{r1} {r2} -> r+-commute r1 r2
  ; isSet-Domain = isSet-Rotation
  }

instance
  AdditiveCommMonoid-Rotation : AdditiveCommMonoid Rotation
  AdditiveCommMonoid-Rotation = record { comm-monoid = CommMonoid-Rotation }

  AdditiveGroup-Rotation : AdditiveGroup AdditiveCommMonoid-Rotation
  AdditiveGroup-Rotation = record { -_ = r-_ ; +-inverse = \{r} -> r+-inverse r }

Group-Rotation : GroupStr Rotation
Group-Rotation = AdditiveGroup.group-str AdditiveGroup-Rotation

abstract
  r--distrib-r+ : (r1 r2 : Rotation) -> (- (r1 + r2)) == (- r1) + (- r2)
  r--distrib-r+ = CommMonoidʰ.preserves-∙ (GroupStr.inverse-CMʰ Group-Rotation)

NonTrivialRotation : Pred Rotation ℓ-one
NonTrivialRotation r = ⟨ Rotation.dir r ⟩ v# xaxis-vector

r+-reflects-NonTrivial :
  (r1 r2 : Rotation) -> NonTrivialRotation (r1 + r2) ->
  ∥ NonTrivialRotation r1 ⊎ NonTrivialRotation r2 ∥
r+-reflects-NonTrivial r1@(rotation (v1 , p1)) r2@(rotation (v2 , p2)) =
  ∥-bind handle
  where
  x1 = vector-index v1 x-axis
  y1 = vector-index v1 y-axis
  x2 = vector-index v2 x-axis
  y2 = vector-index v2 y-axis
  path1 = eqInv (isUnitVector'-equiv v1) p1
  v12 = ⟨ Rotation.dir (r1 r+ r2) ⟩

  Ans = ∥ NonTrivialRotation r1 ⊎ NonTrivialRotation r2 ∥
  handle : Σ[ a ∈ Axis ] (vector-index v12 a # vector-index xaxis-vector a) -> Ans
  handle (x-axis , v#axis) = ∥-bind handle2 (+-reflects-#0 xys#0)
    where
    xys-path : ((x1 * (x2 + (- x1))) + (y1 * (- (y2 + y1)))) ==
               ((x1 * x2) + (- (y1 * y2))) + (- 1#)
    xys-path =
      +-cong (*-distrib-+-left >=>
              +-right minus-extract-right)
             (minus-extract-right >=>
              cong -_ *-distrib-+-left >=>
              minus-distrib-plus) >=>
      +-assoc >=> (+-right (sym +-assoc >=> +-left +-commute >=> +-assoc)) >=> sym +-assoc >=>
      +-right (sym minus-distrib-plus >=> cong -_ path1)

    xys#0 : ((x1 * (x2 + (- x1))) + (y1 * (- (y2 + y1)))) # 0#
    xys#0 = subst2 _#_ (sym xys-path) +-inverse (+₂-preserves-# v#axis)

    handle2 : ((x1 * (x2 + (- x1))) # 0#) ⊎ ((y1 * (- (y2 + y1))) # 0#) -> Ans
    handle2 (inj-l xs#0) = ∥-bind handle3 (comparison-# x2 1# x1 x2#x1)
      where
      x2-x1#0 : (x2 + (- x1)) # 0#
      x2-x1#0 = *₁-reflects-#0 xs#0
      x2#x1 : x2 # x1
      x2#x1 = subst2 _#_ (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
                         +-left-zero (+₂-preserves-# x2-x1#0)
      handle3 : (x2 # 1#) ⊎ (1# # x1) -> Ans
      handle3 (inj-l x2#1) = ∣ inj-r (∣ x-axis , x2#1 ∣) ∣
      handle3 (inj-r 1#x1) = ∣ inj-l (∣ x-axis , sym-# 1#x1 ∣) ∣
    handle2 (inj-r ys#0) = ∣ inj-l (∣ y-axis , *₂-reflects-#0 ys#0 ∣) ∣

  handle (y-axis , v#axis) = ∥-bind handle2 (+-reflects-#0 v#axis)
    where
    handle2 : ((x1 * y2) # 0#) ⊎ ((y1 * x2) # 0#) -> Ans
    handle2 (inj-l x1y2#0) = ∣ inj-r (∣ y-axis , *₁-reflects-#0 x1y2#0 ∣) ∣
    handle2 (inj-r y1x2#0) = ∣ inj-l (∣ y-axis , *₂-reflects-#0 y1x2#0 ∣) ∣

r--preserves-NonTrivial : (r : Rotation) -> NonTrivialRotation r -> NonTrivialRotation (r- r)
r--preserves-NonTrivial r@(rotation (v , _)) = ∥-map handle
  where
  c = conjugate-vector v
  cy = vector-index c y-axis

  handle : Σ[ a ∈ Axis ] (vector-index v a # vector-index xaxis-vector a) ->
           Σ[ a ∈ Axis ] (vector-index c a # vector-index xaxis-vector a)
  handle (x-axis , vx#1) = (x-axis , vx#1)
  handle (y-axis , vy#0) = (y-axis , subst (cy #_) minus-zero (minus-reflects-# vy#0))

¬NonTrivial-zero-rotation : ¬ (NonTrivialRotation zero-rotation)
¬NonTrivial-zero-rotation = irrefl-#

¬NonTrivial->zero-rotation : {r : Rotation} -> ¬ (NonTrivialRotation r) -> (r == zero-rotation)
¬NonTrivial->zero-rotation {r} rv#0 = rotation-ext (direction-ext (tight-# rv#0))


record _r#_ (r1 r2 : Rotation) : Type₁ where
  constructor r#-cons
  field
    NonTrivial-diff : NonTrivialRotation (r2 r+ (r- r1))

irrefl-r# : Irreflexive _r#_
irrefl-r# {r} (r#-cons nt) =
  ¬NonTrivial-zero-rotation (subst NonTrivialRotation (r+-inverse r) nt)

sym-r# : Symmetric _r#_
sym-r# {r1} {r2} (r#-cons nt) = (r#-cons rev-nt)
  where
  d = r2 r+ (r- r1)
  rev-nt = subst NonTrivialRotation (r--distrib-r+ r2 (r- r1) >=>
                                     r+-commute (r- r2) (r- (r- r1)) >=>
                                     cong (_r+ (r- r2)) (r--double-inverse r1))
                 (r--preserves-NonTrivial d nt)

comparison-r# : Comparison _r#_
comparison-r# r1 r2 r3 (r#-cons r1#r3) =
  ∥-map (⊎-swap ∘ ⊎-map r#-cons r#-cons)
    (r+-reflects-NonTrivial (r3 r+ (r- r2)) (r2 r+ (r- r1)) NonTrivial-r3r2-r2r1)
  where
  split-rs : r3 r+ (r- r1) == (r3 r+ (r- r2)) r+ (r2 r+ (r- r1))
  split-rs =
    sym (r+-left-zero _) >=>
    cong (_r+ (r3 r+ (r- r1))) (sym (r+-inverse r2)) >=>
    r+-assoc r2 (r- r2) (r3 r+ (r- r1)) >=>
    r+-commute r2 ((r- r2) r+ (r3 r+ (r- r1))) >=>
    cong (_r+ r2) (sym (r+-assoc (r- r2) r3 (r- r1))) >=>
    r+-assoc ((r- r2) r+ r3) (r- r1) (r2) >=>
    cong2 _r+_ (r+-commute (r- r2) r3) (r+-commute (r- r1) r2)

  NonTrivial-r3r2-r2r1 : NonTrivialRotation ((r3 r+ (r- r2)) r+ (r2 r+ (r- r1)))
  NonTrivial-r3r2-r2r1 = subst NonTrivialRotation split-rs r1#r3

tight-r# : Tight _r#_
tight-r# {r1} {r2} ¬r1#r2 = ans
  where
  path : r2 r+ (r- r1) == zero-rotation
  path = ¬NonTrivial->zero-rotation (¬r1#r2 ∘ r#-cons)

  ans : r1 == r2
  ans = sym (r+-left-zero r1) >=> sym (cong (_r+ r1) path) >=>
        r+-assoc r2 (r- r1) r1 >=> cong (r2 r+_) (r+-commute (r- r1) r1 >=> r+-inverse r1) >=>
        r+-right-zero r2





abstract
  rotate-add-half-rotation : (r : Rotation) (v : Vector) ->
    (rotate (add-half-rotation r) v) == v- (rotate r v)
  rotate-add-half-rotation r@(rotation (dv , _)) v = vector-ext f
    where
    dx = vector-index dv x-axis
    dy = vector-index dv y-axis
    vx = vector-index v x-axis
    vy = vector-index v y-axis

    f : (a : Axis) -> (vector-index (rotate (add-half-rotation r) v) a) ==
                      (vector-index (v- (rotate r v)) a)
    f x-axis = ans
      where
      ans : (- dx) * vx + (- ((- dy) * vy)) == - (dx * vx + (- (dy * vy)))
      ans = +-cong minus-extract-left (cong -_ minus-extract-left) >=>
            sym minus-distrib-plus
    f y-axis = ans
      where
      ans : (- dx) * vy + (- dy) * vx == - (dx * vy + dy * vx)
      ans = +-cong minus-extract-left minus-extract-left >=> sym minus-distrib-plus

  rotate-v- : (r : Rotation) (v : Vector) -> (rotate r (v- v)) == v- (rotate r v)
  rotate-v- r@(rotation (dv , _)) v = vector-ext f
    where
    dx = vector-index dv x-axis
    dy = vector-index dv y-axis
    vx = vector-index v x-axis
    vy = vector-index v y-axis

    f : (a : Axis) -> (vector-index (rotate r (v- v)) a) == (vector-index (v- (rotate r v)) a)
    f x-axis = ans
      where
      ans : dx * (- vx) + (- (dy * (- vy))) == - (dx * vx + (- (dy * vy)))
      ans = +-cong minus-extract-right (cong -_ minus-extract-right) >=>
            sym minus-distrib-plus
    f y-axis = ans
      where
      ans : dx * (- vy) + dy * (- vx) == - (dx * vy + dy * vx)
      ans = +-cong minus-extract-right minus-extract-right >=> sym minus-distrib-plus




  conjugate-distrib-rotate :
    (r : Rotation) (v : Vector) ->
    (conjugate-vector (rotate r v)) == (rotate (r- r) (conjugate-vector v))
  conjugate-distrib-rotate r@(rotation (dv , _)) v = vector-ext f
    where
    f : (a : Axis) -> (vector-index (conjugate-vector (rotate r v)) a) ==
                      (vector-index (rotate (r- r) (conjugate-vector v)) a)
    f x-axis = +-right (cong -_ (sym minus-extract-both))
    f y-axis = minus-distrib-plus >=> +-cong (sym minus-extract-right) (sym minus-extract-left)


  conjugate-distrib-rotate-direction :
    (r : Rotation) (d : Direction) ->
    (conjugate-direction (rotate-direction r d)) ==
    (rotate-direction (r- r) (conjugate-direction d))
  conjugate-distrib-rotate-direction r d = direction-ext (conjugate-distrib-rotate r ⟨ d ⟩)




  direction-diff-step : (d1 d2 : Direction) -> (direction-shift d1 (direction-diff d1 d2)) == d2
  direction-diff-step d1 d2 =
    sym (rotate-direction-assoc r2 (r- r1) d1) >=>
    cong (rotate-direction r2) (cong Rotation.dir (r+-commute (r- r1) r1 >=> r+-inverse r1)) >=>
    cong Rotation.dir (r+-commute r2 zero-rotation >=> r+-left-zero r2)
    where
    r1 = rotation d1
    r2 = rotation d2



isEquiv-rotate : (r : Rotation) -> isEquiv (rotate r)
isEquiv-rotate r = snd (isoToEquiv i)
  where
  open Iso
  i : Iso Vector Vector
  i .fun = rotate r
  i .inv = rotate (r- r)
  i .rightInv v = rotate-assoc r (r- r) v >=>
                  cong (\r -> rotate r v) (r+-inverse r) >=>
                  rotate-zero-rotation v
  i .leftInv v = rotate-assoc (r- r) r v >=>
                 cong (\r -> rotate r v) (r+-commute (r- r) r >=> r+-inverse r) >=>
                 rotate-zero-rotation v

rotate-preserves-+ :
  (r : Rotation) (v1 v2 : Vector) ->
  rotate r (v1 v+ v2) == rotate r v1 v+ rotate r v2
rotate-preserves-+ r@(rotation (dv , _)) v1 v2 = \i -> direct-product-cons (\a -> (f a i))
  where
  dx = direct-product-index dv x-axis
  dy = direct-product-index dv y-axis
  v1x = direct-product-index v1 x-axis
  v1y = direct-product-index v1 y-axis
  v2x = direct-product-index v2 x-axis
  v2y = direct-product-index v2 y-axis

  f : (a : Axis) -> (direct-product-index (rotate r (v1 v+ v2)) a) ==
                    (direct-product-index (rotate r v1 v+ rotate r v2) a)
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
  (r : Rotation) (k : ℝ) (v : Vector) ->
  rotate r (k v* v) == k v* (rotate r v)
rotate-preserves-* r@(rotation (dv , _)) k v = \i -> direct-product-cons (\a -> (f a i))
  where
  dx = direct-product-index dv x-axis
  dy = direct-product-index dv y-axis
  vx = direct-product-index v x-axis
  vy = direct-product-index v y-axis

  f : (a : Axis) -> (direct-product-index (rotate r (k v* v)) a) ==
                    (direct-product-index (k v* (rotate r v)) a)
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

isLinearTransformation-rotate : (r : Rotation) -> isLinearTransformation (rotate r)
isLinearTransformation-rotate r =
  is-linear-transformation (rotate-preserves-+ r) (rotate-preserves-* r)








-- Rotated basis and semi-direction-distance
-- TODO find it a better home

rotated-basis : Rotation -> Axis -> Vector
rotated-basis r = (rotate r) ∘ axis-basis

direction-basis : Direction -> Axis -> Vector
direction-basis d = (rotate (direction-diff xaxis-dir d)) ∘ axis-basis

isBasis-rotated-basis : (r : Rotation) -> isBasis (rotated-basis r)
isBasis-rotated-basis r =
  transform-basis (isLinearTransformation-rotate r)
                  (isEquiv-rotate r)
                  isBasis-axis-basis

isBasis-direction-basis : (d : Direction) -> isBasis (direction-basis d)
isBasis-direction-basis d =
  transform-basis (isLinearTransformation-rotate r)
                  (isEquiv-rotate r)
                  isBasis-axis-basis
  where
  r = (direction-diff xaxis-dir d)

rotated-basis-x-axis : (r : Rotation) -> rotated-basis r x-axis == ⟨ Rotation.dir r ⟩
rotated-basis-x-axis r = cong (fst ∘ Rotation.dir) (p1 >=> p2)
  where
  p1 : r r+ zero-rotation == zero-rotation r+ r
  p1 = r+-commute r zero-rotation

  p2 : zero-rotation r+ r == r
  p2 = r+-left-zero r

direction-basis-x-axis : (d : Direction) -> direction-basis d x-axis == ⟨ d ⟩
direction-basis-x-axis d = cong fst p1
  where
  p1 : direction-shift xaxis-dir (direction-diff xaxis-dir d) == d
  p1 = direction-diff-step xaxis-dir d



semi-direction-distance : (d : Direction) (v : Vector) -> ℝ
semi-direction-distance d v =
  absℝ (basis-decomposition (isBasis-rotated-basis (rotation d)) v y-axis)


semi-direction-distance-v- : (d : Direction) -> {v1 v2 : Vector} -> v1 == (v- v2) ->
  semi-direction-distance d v1 == semi-direction-distance d v2
semi-direction-distance-v- d {v1} {v2} v1=-v2 =
  cong absℝ (dec1=-dec2 y-axis) >=> absℝ-- _
  where

  dec1 : Axis -> ℝ
  dec1 = (basis-decomposition (isBasis-rotated-basis (rotation d)) v1)

  dec2 : Axis -> ℝ
  dec2 = (basis-decomposition (isBasis-rotated-basis (rotation d)) v2)

  dec1=-dec2 : (a : Axis) -> dec1 a == - (dec2 a)
  dec1=-dec2 a =
    cong (\d -> vector-index d a)
      (cong (rotate (rotation (conjugate-direction d))) v1=-v2 >=>
       rotate-v- (rotation (conjugate-direction d)) v2)


sym-semi-direction-distance :
  (d1 d2 : Direction) ->
  semi-direction-distance d1 ⟨ d2 ⟩ == semi-direction-distance d2 ⟨ d1 ⟩
sym-semi-direction-distance d1 d2 =
  cong absℝ (cong (\d -> vector-index ⟨ d ⟩ y-axis) path) >=>
  absℝ-- _
  where
  c = conjugate-direction
  r = rotate-direction

  path : (r (r- (rotation d1)) d2) ==
         (c (r (r- (rotation d2)) d1))
  path = sym (conjugate-distrib-rotate-direction (r- (rotation d2)) d1 >=>
              cong Rotation.dir (r+-commute (r- (r- (rotation d2))) (r- (rotation d1))) >=>
              cong (r (r- (rotation d1))) (conjugate-direction-double-inverse d2))


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
    basis-decomposition (isBasis-rotated-basis (rotation d)) v y-axis == 0#
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
  b = isBasis-rotated-basis (rotation d)

  y0 = semi-direction-distance0->0y d v dis0

  x-path : dv == rotate (rotation d) xaxis-vector
  x-path = sym (rotated-basis-x-axis (rotation d))


direction-span->semi-direction-distance0 :
  (d : Direction) (v : Vector) -> direction-span' d v -> semi-direction-distance d v == 0#
direction-span->semi-direction-distance0 d@(dv , dp) v (k , kdv=v) = ans
  where
  b' = rotated-basis (rotation d)
  b = isBasis-rotated-basis (rotation d)
  c = (basis-decomposition b v)

  x-path : b' x-axis == dv
  x-path = (rotated-basis-x-axis (rotation d))

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
