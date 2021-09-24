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
open import funext
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
  Coords = Axis -> ℝ
  UnitCoords : Pred Coords ℓ-one
  UnitCoords c = axis-dot-product c c == 1ℝ

  raw-rotate : Coords -> Coords -> Coords
  raw-rotate r v = f
    where
    f : Axis -> ℝ
    f x-axis = (r x-axis) * (v x-axis) + (- ((r y-axis) * (v y-axis)))
    f y-axis = (r x-axis) * (v y-axis) + (r y-axis) * (v x-axis)

  raw-rotate-commute : (c1 c2 : Coords) -> raw-rotate c1 c2 == raw-rotate c2 c1
  raw-rotate-commute c1 c2 = funExt f
    where
    f : (a : Axis) -> (raw-rotate c1 c2) a == (raw-rotate c2 c1) a
    f x-axis = +-cong *-commute (cong -_ *-commute)
    f y-axis = +-commute >=> +-cong *-commute *-commute


  raw-rotate-dot-product :
    (r v : Coords) ->
    axis-dot-product (raw-rotate r v) (raw-rotate r v) ==
    (axis-dot-product r r) * (axis-dot-product v v)
  raw-rotate-dot-product r v = reorder
    where
    rx = r x-axis
    ry = r y-axis
    vx = v x-axis
    vy = v y-axis

    reorder : (rx * vx + (- (ry * vy))) * (rx * vx + (- (ry * vy))) +
              (rx * vy + ry * vx) * (rx * vy + ry * vx) ==
              (rx * rx + ry * ry) * (vx * vx + vy * vy)
    reorder = RingSolver.solve ℝRing 4
              (\rx ry vx vy ->
                (rx ⊗ vx ⊕ (⊖ (ry ⊗ vy))) ⊗ (rx ⊗ vx ⊕ (⊖ (ry ⊗ vy))) ⊕
                (rx ⊗ vy ⊕ ry ⊗ vx) ⊗ (rx ⊗ vy ⊕ ry ⊗ vx),
                (rx ⊗ rx ⊕ ry ⊗ ry) ⊗ (vx ⊗ vx ⊕ vy ⊗ vy))
              refl rx ry vx vy


record Rotation : Type₁ where
  no-eta-equality
  constructor rotation-cons
  field
    c : Coords
    len=1 : axis-dot-product c c == 1ℝ

  v : Vector
  v = vector-cons c

  dir : Direction
  dir = v , a.path
    where
    module a where
      abstract
        path : vector-length v == 1#
        path = eqFun (isUnitVector'-equiv v) len=1


rotation->coords : Rotation -> Coords
rotation->coords (rotation-cons c _) = c

rotation-ext : {r1 r2 : Rotation} -> (Rotation.c r1) == (Rotation.c r2) -> r1 == r2
rotation-ext {r1@(rotation-cons _ l1)} {r2@(rotation-cons _ l2)} p = a.path
  where
  module a where
    abstract
      path-l : PathP (\ i -> axis-dot-product (p i) (p i) == 1ℝ)
                     (Rotation.len=1 r1) (Rotation.len=1 r2)
      path-l = isProp->PathP (\i -> isSet-ℝ _ _) l1 l2

      path : r1 == r2
      path i = rotation-cons (p i) (path-l i)

isSet-Rotation : isSet Rotation
isSet-Rotation = isSet-Retract forward backward path isSet-T
  where
  T : Type₁
  T = Σ Coords UnitCoords

  isSet-T : isSet T
  isSet-T = isSetΣ (isSetΠ (\_ -> isSet-ℝ)) (\_ -> (isProp->isSet (isSet-ℝ _ _)))

  forward : Rotation -> T
  forward (rotation-cons c p) = c , p
  backward : T -> Rotation
  backward (c , p) = (rotation-cons c p)
  path : (r : Rotation) -> backward (forward r) == r
  path (rotation-cons c p) = refl


zero-rotation-coords : Coords
zero-rotation-coords = xaxis-coords

zero-rotation : Rotation
zero-rotation = rotation-cons zero-rotation-coords a.path
  where
  module a where
    abstract
     path : axis-dot-product zero-rotation-coords zero-rotation-coords == 1#
     path = +-cong *-right-one *-right-zero >=> +-right-zero

add-half-rotation : Rotation -> Rotation
add-half-rotation r = rotation-cons c a.path
  where
  c = -_ ∘ (Rotation.c r)
  module a where
    abstract
      path : axis-dot-product c c == 1#
      path = +-cong minus-extract-both minus-extract-both >=> (Rotation.len=1 r)

half-rotation : Rotation
half-rotation = add-half-rotation zero-rotation


module _ where
  private
    module ops where
      _r+ᵉ_ : Rotation -> Rotation -> Rotation
      _r+ᵉ_ r1 r2 .Rotation.c = (raw-rotate (Rotation.c r1) (Rotation.c r2))
      _r+ᵉ_ r1 r2 .Rotation.len=1 =
        raw-rotate-dot-product c1 c2 >=> *-cong p1 p2 >=> *-left-one
        where
        c1 = Rotation.c r1
        c2 = Rotation.c r2
        p1 = Rotation.len=1 r1
        p2 = Rotation.len=1 r2

      r-ᵉ_ : Rotation -> Rotation
      r-ᵉ_ r .Rotation.c = conjugate-coords (Rotation.c r)
      r-ᵉ_ r .Rotation.len=1 = +-right minus-extract-both >=> (Rotation.len=1 r)

      module _ where
        _r+_ : Rotation -> Rotation -> Rotation
        _r+_ = _r+ᵉ_

        r-_ : Rotation -> Rotation
        r-_ = r-ᵉ_

        r+-eval : (a b : Rotation) -> a r+ b == a r+ᵉ b
        r+-eval _ _ = refl
        r--eval : (a : Rotation) -> r- a == r-ᵉ a
        r--eval _ = refl

        r+-commute : (r1 r2 : Rotation) -> r1 r+ r2 == r2 r+ r1
        r+-commute (rotation-cons c1 _) (rotation-cons c2 _) =
          rotation-ext (raw-rotate-commute c1 c2)

        raw-rotate-zero-rotation : (c : Coords) -> (raw-rotate zero-rotation-coords c) == c
        raw-rotate-zero-rotation c = funExt f
          where
          f : (a : Axis) -> ((raw-rotate zero-rotation-coords c) a) == (c a)
          f x-axis = +-cong *-left-one (cong -_ *-left-zero >=> minus-zero) >=> +-right-zero
          f y-axis = +-cong *-left-one *-left-zero >=> +-right-zero

        r+-left-zero : (r : Rotation) -> (zero-rotation r+ r) == r
        r+-left-zero (rotation-cons c _) = rotation-ext (raw-rotate-zero-rotation c)

        r+-right-zero : (r : Rotation) -> (r r+ zero-rotation) == r
        r+-right-zero r = r+-commute r zero-rotation >=> r+-left-zero r

        raw-rotate-assoc : (c1 c2 c3 : Coords) ->
                           (raw-rotate (raw-rotate c1 c2) c3) ==
                           (raw-rotate c1 (raw-rotate c2 c3))
        raw-rotate-assoc c1 c2 c3 = sym (funExt f)
          where
          c1x = c1 x-axis
          c1y = c1 y-axis
          c2x = c2 x-axis
          c2y = c2 y-axis
          c3x = c3 x-axis
          c3y = c3 y-axis

          f : (a : Axis) ->
                (raw-rotate c1 (raw-rotate c2 c3)) a ==
                (raw-rotate (raw-rotate c1 c2) c3) a
          f x-axis =
            RingSolver.solve ℝRing 6
              (\c1x c1y c2x c2y c3x c3y ->
                c1x ⊗ (c2x ⊗ c3x ⊕ (⊖ (c2y ⊗ c3y))) ⊕ (⊖ (c1y ⊗ (c2x ⊗ c3y ⊕ (c2y ⊗ c3x)))) ,
                ((c1x ⊗ c2x ⊕ (⊖ (c1y ⊗ c2y))) ⊗ c3x) ⊕ (⊖ ((c1x ⊗ c2y ⊕ c1y ⊗ c2x) ⊗ c3y)))
              refl c1x c1y c2x c2y c3x c3y
          f y-axis =
            RingSolver.solve ℝRing 6
              (\c1x c1y c2x c2y c3x c3y ->
                c1x ⊗ (c2x ⊗ c3y ⊕ c2y ⊗ c3x) ⊕ c1y ⊗ (c2x ⊗ c3x ⊕ (⊖ (c2y ⊗ c3y))) ,
                ((c1x ⊗ c2x ⊕ (⊖ (c1y ⊗ c2y))) ⊗ c3y) ⊕ ((c1x ⊗ c2y ⊕ c1y ⊗ c2x) ⊗ c3x))
              refl c1x c1y c2x c2y c3x c3y

        r+-assoc : (r1 r2 r3 : Rotation) -> (r1 r+ r2) r+ r3 == r1 r+ (r2 r+ r3)
        r+-assoc (rotation-cons c1 _) (rotation-cons c2 _) (rotation-cons c3 _) =
          rotation-ext (raw-rotate-assoc c1 c2 c3)

        r+-inverse : (r : Rotation) -> (r r+ (r- r)) == zero-rotation
        r+-inverse (rotation-cons c p) =
          rotation-ext (funExt f)
          where
          v = vector-cons c
          f : (a : Axis) -> ((raw-rotate c (vector-index (conjugate-vector v))) a) ==
                            (vector-index xaxis-vector a)
          f x-axis = +-right (cong -_ minus-extract-right >=> minus-double-inverse) >=> p
          f y-axis = +-cong minus-extract-right *-commute >=> +-commute >=> +-inverse


  open ops public


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


add-half-rotation-path : (r : Rotation) -> add-half-rotation r == r + half-rotation
add-half-rotation-path r@(rotation-cons c l=1) = a.ans
  where
  module a where
    abstract
      path2 : (a : Axis) -> (- (c a)) == Rotation.c (r r+ᵉ half-rotation) a
      path2 x-axis = sym (+-cong (minus-extract-right >=> cong -_ *-right-one)
                                 (cong -_ (*-right minus-zero >=> *-right-zero) >=> minus-zero) >=>
                          +-right-zero)
      path2 y-axis = sym (+-cong (*-right minus-zero >=> *-right-zero)
                                 (minus-extract-right >=> cong -_ *-right-one) >=>
                          +-left-zero)

      path : add-half-rotation r == r r+ᵉ half-rotation
      path = rotation-ext (funExt path2)

      ans : add-half-rotation r == r r+ half-rotation
      ans = path >=> sym (r+-eval r half-rotation)

minus-half-rotation : - half-rotation == half-rotation
minus-half-rotation = a.ans
  where
  module a where
    abstract
      inner : r-ᵉ half-rotation == half-rotation
      inner = rotation-ext (funExt (\{ x-axis -> refl ; y-axis -> cong -_ minus-zero }))

      ans : - half-rotation == half-rotation
      ans = r--eval half-rotation >=> inner

add-half-rotation-minus-commute :
  (r : Rotation) -> add-half-rotation (- r) == - (add-half-rotation r)
add-half-rotation-minus-commute r =
  add-half-rotation-path (- r) >=>
  +-right (sym minus-half-rotation) >=>
  sym minus-distrib-plus >=>
  cong -_ (sym (add-half-rotation-path r))

add-half-rotation-double-inverse : (r : Rotation) ->
  add-half-rotation (add-half-rotation r) == r
add-half-rotation-double-inverse _ =
  add-half-rotation-path _ >=>
  +-left (add-half-rotation-path _) >=>
  +-assoc >=>
  +-right (+-right (sym minus-half-rotation) >=>
           +-inverse) >=>
  +-right-zero





record NonTrivialRotation (r : Rotation) : Type₁ where
  no-eta-equality
  constructor non-trivial-rotation
  field
    apart : ⟨ Rotation.dir r ⟩ v# xaxis-vector

isProp-NonTrivialRotation : {r : Rotation} -> isProp (NonTrivialRotation r)
isProp-NonTrivialRotation (non-trivial-rotation a1) (non-trivial-rotation a2) =
  cong non-trivial-rotation (isProp-# a1 a2)

r+ᵉ-reflects-NonTrivial :
  (r1 r2 : Rotation) -> NonTrivialRotation (r1 r+ᵉ r2) ->
  ∥ NonTrivialRotation r1 ⊎ NonTrivialRotation r2 ∥
r+ᵉ-reflects-NonTrivial r1@(rotation-cons c1 p1) r2@(rotation-cons c2 p2) =
  ∥-bind handle ∘ NonTrivialRotation.apart
  where
  x1 = c1 x-axis
  y1 = c1 y-axis
  x2 = c2 x-axis
  y2 = c2 y-axis
  v12 = ⟨ Rotation.dir (r1 r+ᵉ r2) ⟩

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
      +-right (sym minus-distrib-plus >=> cong -_ p1)

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
      handle3 (inj-l x2#1) = ∣ inj-r (non-trivial-rotation (∣ x-axis , x2#1 ∣)) ∣
      handle3 (inj-r 1#x1) = ∣ inj-l (non-trivial-rotation (∣ x-axis , sym-# 1#x1 ∣)) ∣
    handle2 (inj-r ys#0) = ∣ inj-l (non-trivial-rotation (∣ y-axis , *₂-reflects-#0 ys#0 ∣)) ∣

  handle (y-axis , v#axis) = ∥-bind handle2 (+-reflects-#0 v#axis)
    where
    handle2 : ((x1 * y2) # 0#) ⊎ ((y1 * x2) # 0#) -> Ans
    handle2 (inj-l x1y2#0) = ∣ inj-r (non-trivial-rotation (∣ y-axis , *₁-reflects-#0 x1y2#0 ∣)) ∣
    handle2 (inj-r y1x2#0) = ∣ inj-l (non-trivial-rotation (∣ y-axis , *₂-reflects-#0 y1x2#0 ∣)) ∣

r+-reflects-NonTrivial :
  (r1 r2 : Rotation) -> NonTrivialRotation (r1 r+ r2) ->
  ∥ NonTrivialRotation r1 ⊎ NonTrivialRotation r2 ∥
r+-reflects-NonTrivial r1 r2 nt =
  r+ᵉ-reflects-NonTrivial r1 r2 (subst NonTrivialRotation (r+-eval r1 r2) nt)


r-ᵉ-preserves-NonTrivial : (r : Rotation) -> NonTrivialRotation r -> NonTrivialRotation (r-ᵉ r)
r-ᵉ-preserves-NonTrivial r@(rotation-cons coords _) =
  non-trivial-rotation ∘ ∥-map handle ∘ NonTrivialRotation.apart
  where
  v = vector-cons coords
  c = conjugate-vector v
  cy = vector-index c y-axis

  handle : Σ[ a ∈ Axis ] (vector-index v a # vector-index xaxis-vector a) ->
           Σ[ a ∈ Axis ] (vector-index c a # vector-index xaxis-vector a)
  handle (x-axis , vx#1) = (x-axis , vx#1)
  handle (y-axis , vy#0) = (y-axis , subst (cy #_) minus-zero (minus-reflects-# vy#0))

r--preserves-NonTrivial : (r : Rotation) -> NonTrivialRotation r -> NonTrivialRotation (r- r)
r--preserves-NonTrivial r nt =
  subst NonTrivialRotation (sym (r--eval r)) (r-ᵉ-preserves-NonTrivial r nt)


¬NonTrivial-zero-rotation : ¬ (NonTrivialRotation zero-rotation)
¬NonTrivial-zero-rotation = irrefl-# ∘ NonTrivialRotation.apart

¬NonTrivial->zero-rotation : {r : Rotation} -> ¬ (NonTrivialRotation r) -> (r == zero-rotation)
¬NonTrivial->zero-rotation {r} rv#0 =
  rotation-ext (cong vector-index (tight-# (rv#0 ∘ non-trivial-rotation)))

record _r#_ (r1 r2 : Rotation) : Type₁ where
  constructor r#-cons
  field
    NonTrivial-diff : NonTrivialRotation (r2 r+ (r- r1))

isProp-r# : {r1 r2 : Rotation} -> isProp (r1 r# r2)
isProp-r# (r#-cons nt1) (r#-cons nt2) = cong r#-cons (isProp-NonTrivialRotation nt1 nt2)

irrefl-r# : Irreflexive _r#_
irrefl-r# {r} (r#-cons nt) =
  ¬NonTrivial-zero-rotation (subst NonTrivialRotation (r+-inverse r) nt)

sym-r# : Symmetric _r#_
sym-r# {r1} {r2} (r#-cons nt) = (r#-cons rev-nt)
  where
  d = r2 r+ (r- r1)
  rev-nt : NonTrivialRotation (r1 r+ (r- r2))
  rev-nt = subst NonTrivialRotation
                 (minus-distrib-plus >=> +-commute >=> +-left minus-double-inverse)
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

instance
  TightApartnessStr-Rotation : TightApartnessStr Rotation
  TightApartnessStr-Rotation .TightApartnessStr._#_ = _r#_
  TightApartnessStr-Rotation .TightApartnessStr.TightApartness-# =
    tight-r# , (irrefl-r# , sym-r# , comparison-r#)
  TightApartnessStr-Rotation .TightApartnessStr.isProp-# = \x y -> isProp-r#

abstract
  +₁-preserves-r# : {r1 r2 r3 : Rotation} -> r2 # r3 -> (r1 + r2) # (r1 + r3)
  +₁-preserves-r# {r1} {r2} {r3} (r#-cons nt-r2r3) = r#-cons (subst NonTrivialRotation p nt-r2r3)
    where
    p : diff r2 r3 == diff (r1 + r2) (r1 + r3)
    p = sym +-left-zero >=>
        +-left (sym +-inverse) >=>
        +-swap-diff

  +₂-preserves-r# : {r1 r2 r3 : Rotation} -> r1 # r2 -> (r1 + r3) # (r2 + r3)
  +₂-preserves-r# {r1} {r2} {r3} r1#r2 = subst2 _#_ +-commute +-commute (+₁-preserves-r# r1#r2)


-- Rotate Vector

rotate-vector : Rotation -> Vector -> Vector
rotate-vector d v = vector-cons (raw-rotate (Rotation.c d) (vector-index v))

rotate-vector-zero-rotation : (v : Vector) -> (rotate-vector zero-rotation v) == v
rotate-vector-zero-rotation v = cong direct-product-cons (raw-rotate-zero-rotation (vector-index v))

rotate-vector-assoc : (r1 r2 : Rotation) (v : Vector) ->
                      (rotate-vector r1 (rotate-vector r2 v)) == (rotate-vector (r1 r+ r2) v)
rotate-vector-assoc (rotation-cons dv1 _) (rotation-cons dv2 _) v =
  cong vector-cons (sym (raw-rotate-assoc dv1 dv2 (vector-index v)))

abstract
  rotate-add-half-rotation : (r : Rotation) (v : Vector) ->
    (rotate-vector (add-half-rotation r) v) == v- (rotate-vector r v)
  rotate-add-half-rotation r@(rotation-cons dv _) v = vector-ext f
    where
    dx = dv x-axis
    dy = dv y-axis
    vx = vector-index v x-axis
    vy = vector-index v y-axis

    f : (a : Axis) -> (vector-index (rotate-vector (add-half-rotation r) v) a) ==
                      (vector-index (v- (rotate-vector r v)) a)
    f x-axis = ans
      where
      ans : (- dx) * vx + (- ((- dy) * vy)) == - (dx * vx + (- (dy * vy)))
      ans = +-cong minus-extract-left (cong -_ minus-extract-left) >=>
            sym minus-distrib-plus
    f y-axis = ans
      where
      ans : (- dx) * vy + (- dy) * vx == - (dx * vy + dy * vx)
      ans = +-cong minus-extract-left minus-extract-left >=> sym minus-distrib-plus

  rotate-v- : (r : Rotation) (v : Vector) -> (rotate-vector r (v- v)) == v- (rotate-vector r v)
  rotate-v- r@(rotation-cons dv _) v = vector-ext f
    where
    dx = dv x-axis
    dy = dv y-axis
    vx = vector-index v x-axis
    vy = vector-index v y-axis

    f : (a : Axis) -> (vector-index (rotate-vector r (v- v)) a) ==
                      (vector-index (v- (rotate-vector r v)) a)
    f x-axis = ans
      where
      ans : dx * (- vx) + (- (dy * (- vy))) == - (dx * vx + (- (dy * vy)))
      ans = +-cong minus-extract-right (cong -_ minus-extract-right) >=>
            sym minus-distrib-plus
    f y-axis = ans
      where
      ans : dx * (- vy) + dy * (- vx) == - (dx * vy + dy * vx)
      ans = +-cong minus-extract-right minus-extract-right >=> sym minus-distrib-plus

  conjugate-distrib-rotate-vector :
    (r : Rotation) (v : Vector) ->
    (conjugate-vector (rotate-vector r v)) == (rotate-vector (r- r) (conjugate-vector v))
  conjugate-distrib-rotate-vector r@(rotation-cons dv _) v =
    inner >=> cong (\x -> (rotate-vector x (conjugate-vector v))) (sym (r--eval r))
    where
    inner : (conjugate-vector (rotate-vector r v)) == (rotate-vector (r-ᵉ r) (conjugate-vector v))
    inner = vector-ext f
      where
      f : (a : Axis) -> (vector-index (conjugate-vector (rotate-vector r v)) a) ==
                        (vector-index (rotate-vector (r-ᵉ r) (conjugate-vector v)) a)
      f x-axis = +-right (cong -_ (sym minus-extract-both))
      f y-axis = minus-distrib-plus >=> +-cong (sym minus-extract-right) (sym minus-extract-left)


isEquiv-rotate-vector : (r : Rotation) -> isEquiv (rotate-vector r)
isEquiv-rotate-vector r = snd (isoToEquiv i)
  where
  open Iso
  i : Iso Vector Vector
  i .fun = rotate-vector r
  i .inv = rotate-vector (r- r)
  i .rightInv v = rotate-vector-assoc r (r- r) v >=>
                  cong (\r -> rotate-vector r v) (r+-inverse r) >=>
                  rotate-vector-zero-rotation v
  i .leftInv v = rotate-vector-assoc (r- r) r v >=>
                 cong (\r -> rotate-vector r v) (r+-commute (r- r) r >=> r+-inverse r) >=>
                 rotate-vector-zero-rotation v

rotate-vector-preserves-+ :
  (r : Rotation) (v1 v2 : Vector) ->
  rotate-vector r (v1 v+ v2) == rotate-vector r v1 v+ rotate-vector r v2
rotate-vector-preserves-+ r@(rotation-cons dv _) v1 v2 = \i -> direct-product-cons (\a -> (f a i))
  where
  dx = dv x-axis
  dy = dv y-axis
  v1x = direct-product-index v1 x-axis
  v1y = direct-product-index v1 y-axis
  v2x = direct-product-index v2 x-axis
  v2y = direct-product-index v2 y-axis

  f : (a : Axis) -> (direct-product-index (rotate-vector r (v1 v+ v2)) a) ==
                    (direct-product-index (rotate-vector r v1 v+ rotate-vector r v2) a)
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

rotate-vector-preserves-* :
  (r : Rotation) (k : ℝ) (v : Vector) ->
  rotate-vector r (k v* v) == k v* (rotate-vector r v)
rotate-vector-preserves-* r@(rotation-cons dv _) k v = \i -> direct-product-cons (\a -> (f a i))
  where
  dx = dv x-axis
  dy = dv y-axis
  vx = direct-product-index v x-axis
  vy = direct-product-index v y-axis

  f : (a : Axis) -> (direct-product-index (rotate-vector r (k v* v)) a) ==
                    (direct-product-index (k v* (rotate-vector r v)) a)
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

isLinearTransformation-rotate-vector : (r : Rotation) -> isLinearTransformation (rotate-vector r)
isLinearTransformation-rotate-vector r =
  is-linear-transformation (rotate-vector-preserves-+ r) (rotate-vector-preserves-* r)

-- Rotate Direction

rotate-vector-preserves-vector-length² :
  (r : Rotation) (v : Vector) -> vector-length² (rotate-vector r v) == vector-length² v
rotate-vector-preserves-vector-length² (rotation-cons dv vl-d=1) v =
  raw-rotate-dot-product dv (vector-index v) >=>
  *-left vl-d=1 >=>
  *-left-one

rotate-preserves-vector-length :
  (r : Rotation) (v : Vector) -> vector-length (rotate-vector r v) == vector-length v
rotate-preserves-vector-length r v =
  cong2-dep sqrtℝ p (isProp->PathP (\i -> isProp-≤ 0ℝ (p i)) _ _)
  where
  p = rotate-vector-preserves-vector-length² r v

rotate-direction : Rotation -> Direction -> Direction
rotate-direction r (v , vl=1) = rotate-vector r v , a.vl=1'
  where
  module a where
    abstract
      vl=1' : vector-length (rotate-vector r v) == 1#
      vl=1' = rotate-preserves-vector-length r v >=> vl=1

rotate-direction-zero-rotation : (d : Direction) -> (rotate-direction zero-rotation d) == d
rotate-direction-zero-rotation d =  direction-ext (rotate-vector-zero-rotation ⟨ d ⟩)

rotate-direction-assoc :
  (r1 r2 : Rotation) (d : Direction) ->
  (rotate-direction r1 (rotate-direction r2 d)) == (rotate-direction (r1 r+ r2) d)
rotate-direction-assoc r1 r2 d = direction-ext (rotate-vector-assoc r1 r2 ⟨ d ⟩)


direction->rotation : Direction -> Rotation
direction->rotation (v , p) = rotation-cons (vector-index v) a.path
  where
  module a where
    abstract
      path : vector-length² v == 1#
      path = (eqInv (isUnitVector'-equiv v) p)

direction-diff : Direction -> Direction -> Rotation
direction-diff d1 d2 = diff (direction->rotation d1) (direction->rotation d2)

direction-shift : Direction -> Rotation -> Direction
direction-shift d r = rotate-direction r d


abstract
  direction-diff-anticommute : (d1 d2 : Direction) ->
    (direction-diff d1 d2) == - (direction-diff d2 d1)
  direction-diff-anticommute d1 d2 =
    sym (minus-distrib-plus >=> +-commute >=> +-left minus-double-inverse)


  rotate-direction-commute : (d1 d2 : Direction) ->
    rotate-direction (direction->rotation d1) d2 ==
    rotate-direction (direction->rotation d2) d1
  rotate-direction-commute d1 d2 = direction-ext (cong vector-cons (raw-rotate-commute _ _))


  direction-diff-trans : (d1 d2 d3 : Direction) ->
    (direction-diff d1 d2) r+ (direction-diff d2 d3) ==
    (direction-diff d1 d3)
  direction-diff-trans _ _ _ = diff-trans

  direction-shift-diff : (d1 d2 d3 : Direction) ->
    direction-shift d1 (direction-diff d2 d3) ==
    direction-shift d3 (direction-diff d2 d1)
  direction-shift-diff d1 d2 d3 =
    cong (direction-shift d1) +-commute >=>
    sym (rotate-direction-assoc _ _ _) >=>
    cong (rotate-direction (r- (direction->rotation d2)))
      (rotate-direction-commute d3 d1) >=>
    (rotate-direction-assoc _ _ _) >=>
    cong (direction-shift d3) +-commute

  direction-diff-shift : (d1 d2 : Direction) (r : Rotation) ->
    direction-diff d1 (direction-shift d2 r) ==
    direction-diff d1 d2 r+ r
  direction-diff-shift d1 d2 r =
    +-commute >=>
    +-right (rotation-ext refl >=> +-commute) >=>
    sym +-assoc >=>
    +-left +-commute

  conjugate-distrib-rotate-direction :
    (r : Rotation) (d : Direction) ->
    (conjugate-direction (rotate-direction r d)) ==
    (rotate-direction (- r) (conjugate-direction d))
  conjugate-distrib-rotate-direction r d = direction-ext (conjugate-distrib-rotate-vector r ⟨ d ⟩)

  r-ᵉ-direction->rotation : (d : Direction) ->
    (r-ᵉ (direction->rotation d)) == (direction->rotation (conjugate-direction d))
  r-ᵉ-direction->rotation d = rotation-ext refl

  r--direction->rotation : (d : Direction) ->
    (r- (direction->rotation d)) == (direction->rotation (conjugate-direction d))
  r--direction->rotation d = r--eval (direction->rotation d) >=> r-ᵉ-direction->rotation d

  add-half-rotation-direction->rotation : (d : Direction) ->
    (add-half-rotation (direction->rotation d)) == (direction->rotation (d- d))
  add-half-rotation-direction->rotation d =
    rotation-ext (funExt (\a -> refl))

  rotate-direction-add-half-rotation : (r : Rotation) (d : Direction) ->
    (rotate-direction (add-half-rotation r) d) == d- (rotate-direction r d)
  rotate-direction-add-half-rotation r d =
    direction-ext (rotate-add-half-rotation r ⟨ d ⟩)

  direction-diff-minus-left : (d1 d2 : Direction) ->
    (direction-diff (d- d1) d2) == add-half-rotation (direction-diff d1 d2)
  direction-diff-minus-left d1 d2 =
    +-right (cong r-_ (sym (add-half-rotation-direction->rotation _) >=>
                       add-half-rotation-path (direction->rotation d1)) >=>
             minus-distrib-plus >=>
             +-right minus-half-rotation) >=>
    sym +-assoc >=>
    sym (add-half-rotation-path _)

  direction-diff-minus-right : (d1 d2 : Direction) ->
    (direction-diff d1 (d- d2)) == add-half-rotation (direction-diff d1 d2)
  direction-diff-minus-right d1 d2 =
    +-commute >=>
    +-right (sym (add-half-rotation-direction->rotation _) >=>
             add-half-rotation-path (direction->rotation d2)) >=>
    sym +-assoc >=>
    +-left +-commute >=>
    sym (add-half-rotation-path _)


  rotate-direction-self-diff' : (d : Direction) -> direction-diff d d == zero-rotation
  rotate-direction-self-diff' d = +-inverse

  direction-diff-step : (d1 d2 : Direction) -> (direction-shift d1 (direction-diff d1 d2)) == d2
  direction-diff-step d1 d2 =
    cong (direction-shift d1) +-commute >=>
    sym (rotate-direction-assoc (- r1) r2 d1) >=>
    cong (rotate-direction (- r1)) (rotate-direction-commute d2 d1) >=>
    rotate-direction-assoc (- r1) r1 d2 >=>
    cong (direction-shift d2) (+-commute >=> +-inverse) >=>
    rotate-direction-zero-rotation d2
    where
    r1 = direction->rotation d1
    r2 = direction->rotation d2





-- Rotated basis and semi-direction-distance
-- TODO find it a better home

--rotated-basis : Rotation -> Axis -> Vector
--rotated-basis r = (rotate-vector r) ∘ axis-basis
--
--isBasis-rotated-basis : (r : Rotation) -> isBasis (rotated-basis r)
--isBasis-rotated-basis r =
--  transform-basis (isLinearTransformation-rotate-vector r)
--                  (isEquiv-rotate-vector r)
--                  isBasis-axis-basis
--rotated-basis-x-axis : (r : Rotation) -> rotated-basis r x-axis == ⟨ Rotation.dir r ⟩
--rotated-basis-x-axis r = cong (fst ∘ Rotation.dir) (p1 >=> p2)
--  where
--  p1 : r r+ zero-rotation == zero-rotation r+ r
--  p1 = r+-commute r zero-rotation
--
--  p2 : zero-rotation r+ r == r
--  p2 = r+-left-zero r

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



semi-direction-distance : (d : Direction) (v : Vector) -> ℝ
semi-direction-distance d v =
  absℝ (basis-decomposition (isBasis-direction-basis d) v y-axis)


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
