{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.vector where

open import apartness
open import base
open import commutative-monoid
open import cubical using (_≃_ ; isEquiv)
open import direct-product
open import direct-product.standard-basis
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finset.instances
open import finsum
open import functions
open import funext
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import isomorphism
open import order
open import order.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
open import real.arithmetic.absolute-value
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.sqrt
open import real.arithmetic.sqrt.base
open import real.heyting-field
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import set-quotient
open import sigma
open import subset
open import solver
open import truncation
open import univalence
open import vector-space
open import vector-space.finite


data Axis : Type₀ where
 x-axis : Axis
 y-axis : Axis

x-axis≠y-axis : x-axis != y-axis
x-axis≠y-axis x=y = subst f x=y tt
  where
  f : Axis -> Type₀
  f x-axis = Top
  f y-axis = Bot

isFinSet-Axis : isFinSet Axis
isFinSet-Axis = ∣ 2 , eq2 ∣
  where
  abstract
    forward : Axis -> Top ⊎ Top
    forward x-axis = inj-l tt
    forward y-axis = inj-r tt

    backward : Top ⊎ Top -> Axis
    backward (inj-l _) = x-axis
    backward (inj-r _) = y-axis

    fb : (i : Top ⊎ Top) -> forward (backward i) == i
    fb (inj-l _) = refl
    fb (inj-r _) = refl

    bf : (a : Axis) -> backward (forward a) == a
    bf x-axis = refl
    bf y-axis = refl

    i : Iso Axis (Top ⊎ Top)
    i = iso forward backward fb bf

    eq : Axis ≃ (Top ⊎ Top)
    eq = isoToEquiv i

    eq2 : Axis ≃ Fin 2
    eq2 = subst (Axis ≃_) (cong2 _⊎_ (sym Fin-Top) (sym Fin-Top) >=> sym (Fin-+ 1 1)) eq

instance
  FinSetStr-Axis : FinSetStr Axis
  FinSetStr-Axis = record {isFin = isFinSet-Axis}

Vector : Type₁
Vector = DirectProduct ℝ Axis

instance
  VectorSpaceStr-Vector = VectorSpaceStr-DirectProduct ℝField Axis
  ModuleSpaceStr-Vector = VectorSpaceStr.module-str VectorSpaceStr-Vector
  TightApartnessStr-Vector = ModuleStr.TightApartnessStr-V ModuleSpaceStr-Vector

abstract
  axis-merge : {ℓ : Level} {D : Type ℓ} {CM : CommMonoid D} (f : Axis -> D) ->
               finiteMerge CM f == CommMonoid._∙_ CM (f x-axis) (f y-axis)
  axis-merge {CM = CM} f =
    finiteMerge-convert-iso CM (iso⁻¹ i) f >=>
    finiteMerge-⊎ CM _ >=>
    cong2 CM._∙_ (finiteMerge-Top CM _) (finiteMerge-Top CM _)
    where
    module CM = CommMonoid CM
    open Iso
    i : Iso Axis (Top ⊎ Top)
    i .fun x-axis = inj-l tt
    i .fun y-axis = inj-r tt
    i .inv (inj-l _) = x-axis
    i .inv (inj-r _) = y-axis
    i .rightInv (inj-l _) = refl
    i .rightInv (inj-r _) = refl
    i .leftInv x-axis = refl
    i .leftInv y-axis = refl

conjugate-vector : Vector -> Vector
conjugate-vector v = direct-product-cons f
  where
  f : Axis -> ℝ
  f x-axis = direct-product-index v x-axis
  f y-axis = - (direct-product-index v y-axis)

vector-length² : Vector -> ℝ
vector-length² v = (x * x) + (y * y)
  where
  x = (direct-product-index v x-axis)
  y = (direct-product-index v y-axis)

vector-length²≮0 : (v : Vector) -> (vector-length² v ≮ 0ℝ)
vector-length²≮0 v = +-preserves-≮0 (x * x) (y * y) (≮0-square x) (≮0-square y)
  where
  x = (direct-product-index v x-axis)
  y = (direct-product-index v y-axis)

vector-length : Vector -> ℝ
vector-length v = sqrtℝ (vector-length² v) (vector-length²≮0 v)

vector-length≮0 : (v : Vector) -> (vector-length v ≮ 0ℝ)
vector-length≮0 v = sqrt-0≤ (vector-length² v) (vector-length²≮0 v)

vector-length-squared-path : (v : Vector) -> (vector-length v) * (vector-length v) == (vector-length² v)
vector-length-squared-path v = sqrt² (vector-length² v) (vector-length²≮0 v)

isUnitVector : Pred Vector ℓ-one
isUnitVector v = vector-length v == 1ℝ

isProp-isUnitVector : (v : Vector) -> isProp (isUnitVector v)
isProp-isUnitVector v = isSet-ℝ (vector-length v) 1ℝ

isUnitVector' : Pred Vector ℓ-one
isUnitVector' v = vector-length² v == 1ℝ

isProp-isUnitVector' : (v : Vector) -> isProp (isUnitVector' v)
isProp-isUnitVector' v = isSet-ℝ (vector-length² v) 1ℝ

isUnitVector'-equiv : (v : Vector) -> isUnitVector' v ≃ isUnitVector v
isUnitVector'-equiv v =
  isoToEquiv (isProp->iso forward backward (isProp-isUnitVector' v) (isProp-isUnitVector v))
  where
  forward : isUnitVector' v -> isUnitVector v
  forward p = path
    where
    p2 = p >=> sym *-left-one
    0<1 : 0ℝ < 1ℝ
    0<1 = ℚ->ℝ-preserves-< 0r 1r 0<1r

    0≤1 : 0ℝ ≤ 1ℝ
    0≤1 = (weaken-< {_} {_} {_} {_} {_} {_} {0ℝ} {1ℝ} 0<1)

    path : vector-length v == 1#
    path = cong2-dep sqrtℝ p2 (isProp->PathP (\i -> isProp-≤ 0ℝ (p2 i)) _ _) >=>
           sqrt-square 1# >=> absℝ-NonNeg-idem 1# 0≤1

  backward : isUnitVector v -> isUnitVector' v
  backward p = sym (vector-length-squared-path v) >=> *-cong p p >=> *-left-one


Direction : Type₁
Direction = Σ Vector isUnitVector

0<-square : (x : ℝ) -> (x # 0#) -> 0# < (x * x)
0<-square x x#0 = handle (eqInv (<>-equiv-# x 0#) x#0)
  where
  handle : (x < 0# ⊎ 0# < x) -> 0# < (x * x)
  handle (inj-l x<0) = subst (_< (x * x)) *-right-zero (*₁-flips-< x x 0# x<0 x<0)
  handle (inj-r 0<x) = subst (_< (x * x)) *-right-zero (*₁-preserves-< x 0# x 0<x 0<x)

vector-length>0 : (v : Vector) -> (v v# 0v) -> (vector-length v > 0#)
vector-length>0 v v#0 = unsquash (isProp-< 0# (vector-length v)) (∥-map handle v#0)
  where
  x = (direct-product-index v x-axis)
  y = (direct-product-index v y-axis)
  xx = x * x
  yy = y * y
  xxyy = xx + yy

  handle-vl²>0 : (vector-length² v > 0#) -> (vector-length v > 0#)
  handle-vl²>0 = sqrt-0< (vector-length² v) (vector-length²≮0 v)


  handle : Σ[ a ∈ Axis ] (direct-product-index v a) # 0# -> (vector-length v > 0#)
  handle (x-axis , x#0) = handle-vl²>0 (trans-<-≤ {d1 = 0ℝ} {xx} {xxyy}  0<xx xx≤xxyy)
    where
    0<xx : 0# < xx
    0<xx = 0<-square x x#0
    0≤yy : 0# ≤ yy
    0≤yy = ≮0-square y
    xx≤xxyy : xx ≤ xxyy
    xx≤xxyy = subst (_≤ xxyy) +-right-zero (+₁-preserves-≤ xx 0# yy 0≤yy)
  handle (y-axis , y#0) = handle-vl²>0 (trans-<-≤ {d1 = 0ℝ} {yy} {xxyy}  0<yy yy≤xxyy)
    where
    0<yy : 0# < yy
    0<yy = 0<-square y y#0
    0≤xx : 0# ≤ xx
    0≤xx = ≮0-square x
    yy≤xxyy : yy ≤ xxyy
    yy≤xxyy = subst (_≤ xxyy) +-left-zero (+₂-preserves-≤ 0# xx yy 0≤xx)

vector-length>0-#0 : (v : Vector) -> (vector-length v > 0#) -> (v v# 0v)
vector-length>0-#0 v l>0 = unsquash (isProp-v# v 0v) (∥-map handle (+-reflects-#0 vl²#0))
  where
  vl = vector-length v
  vl² = vector-length² v
  x = (direct-product-index v x-axis)
  y = (direct-product-index v y-axis)

  vl#0 : vl # 0#
  vl#0 = eqFun (<>-equiv-# (vector-length v) 0#) (inj-r l>0)
  vl²#0 : vl² # 0#
  vl²#0 = subst (_# 0#) (vector-length-squared-path v) (*₁-preserves-#0 vl#0 vl#0)

  handle : ((x * x) # 0#) ⊎ ((y * y) # 0#) -> v v# 0v
  handle (inj-l xx#0) = ∣ x-axis , *₁-reflects-#0 xx#0 ∣
  handle (inj-r yy#0) = ∣ y-axis , *₁-reflects-#0 yy#0 ∣


vector-length²-* : (k : ℝ) (v : Vector) -> vector-length² (k v* v) == (k * k) * vector-length² v
vector-length²-* k v = p
  where
  x = (direct-product-index v x-axis)
  y = (direct-product-index v y-axis)
  kx = k * x
  ky = k * y

  swap-* : (z : ℝ) -> ((k * z) * (k * z)) == (k * k) * (z * z)
  swap-* z = *-assoc >=> *-right (*-commute >=> *-assoc) >=> sym *-assoc

  p : (kx * kx) + (ky * ky) == (k * k) * ((x * x) + (y * y))
  p = cong2 _+_ (swap-* x) (swap-* y) >=>
      sym *-distrib-+-left

vector-length-* : (k : ℝ) (v : Vector) -> vector-length (k v* v) == (absℝ k) * vector-length v
vector-length-* k v = p6
  where
  l2kv = vector-length² (k v* v)
  l2v = vector-length² v
  lkv = vector-length (k v* v)
  lv = vector-length v
  aklv = (absℝ k * lv)
  0≤l2kv = vector-length²≮0 (k v* v)
  0≤l2v = vector-length²≮0 v
  0≤lv = vector-length≮0 v
  0≤aklv = *-preserves-0≤ _ _ (absℝ-≮0 k) 0≤lv

  p2 : l2v == lv * lv
  p2 = sym (sqrt² l2v 0≤l2v)
  p4 : (k * k) * (lv * lv) == aklv * aklv
  p4 = *-left (absℝ-square k) >=>
       *-assoc >=> *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc
  p3 : l2kv == aklv * aklv
  p3 = vector-length²-* k v >=> *-right p2 >=> p4

  p5 : lkv == sqrtℝ (aklv * aklv) (≮0-square aklv)
  p5 = cong2-dep sqrtℝ p3 (isProp->PathP (\i -> isProp-≤ 0ℝ (p3 i)) 0≤l2kv (≮0-square aklv))

  p6 : lkv == aklv
  p6 = p5 >=> sqrt-square aklv >=> absℝ-NonNeg-idem aklv 0≤aklv

vector-length²-v- : (v : Vector) -> vector-length² (v- v) == vector-length² v
vector-length²-v- v =
  cong vector-length² -v=-1v >=>
  vector-length²-* (- 1ℝ) v >=>
  *-left (minus-extract-both >=> *-right-one) >=>
  *-left-one
  where
  -v=-1v : (v- v) == (- 1ℝ) v* v
  -v=-1v = sym v*-left-minus-one

vector-length-v- : (v : Vector) -> vector-length (v- v) == vector-length v
vector-length-v- v = cong2-dep sqrtℝ p (isProp->PathP (\i -> isProp-≤ 0ℝ (p i)) _ _)
  where
  p = vector-length²-v- v

d-_ : Direction -> Direction
d-_ (v , vl=1) = (v- v , vector-length-v- v >=> vl=1)


normalize-vector : (v : Vector) -> v v# 0v -> Vector
normalize-vector v v#0 = (ℝ1/ (vector-length v) (inj-r (vector-length>0 v v#0))) v* v

normalize-vector-path : (v : Vector) -> (v#0 : v v# 0v) ->
                        v == (vector-length v) v* (normalize-vector v v#0)
normalize-vector-path v v#0 =
  sym (sym v*-assoc >=> cong (_v* v) (*-commute >=> (ℝ1/-inverse vl vl-inv)) >=> v*-left-one)
  where
  vl = (vector-length v)
  vl-inv = (inj-r (vector-length>0 v v#0))

normalize-vector-v*-Pos :
  (v : Vector) -> (v#0 : v v# 0v) -> (k : ℝ) -> (0ℝ < k) -> (kv#0 : (k v* v) v# 0v) ->
  normalize-vector (k v* v) kv#0 == normalize-vector v v#0
normalize-vector-v*-Pos v v#0 k 0<k kv#0 =
  sym (sym v*-left-one >=>
       (cong (_v* nv) (sym *-left-one >=>
                       *-cong (sym (ℝ1/-inverse k k-inv)) (sym (ℝ1/-inverse vl vl-inv)) >=>
                       sym *-assoc >=>
                       *-left (*-commute >=> sym *-assoc >=> *-left *-commute))) >=>
       v*-assoc >=>
       (cong (((ℝ1/ k k-inv * ℝ1/ vl vl-inv) * k) v*_) (sym (normalize-vector-path v v#0))) >=>
       v*-assoc >=>
       (cong ((ℝ1/ k k-inv * ℝ1/ vl vl-inv) v*_) (normalize-vector-path kv kv#0)) >=>
       sym v*-assoc >=>
       cong (_v* nkv) p >=>
       v*-left-one)

  where
  vl = (vector-length v)
  vl-inv = (inj-r (vector-length>0 v v#0))
  k-inv = (inj-r 0<k)
  kv = k v* v
  nv = normalize-vector v v#0
  nkv = normalize-vector kv kv#0
  abs-k-path : absℝ k == k
  abs-k-path = absℝ-NonNeg-idem k (weaken-< {_} {_} {_} {_} {_} {_} {0ℝ} {k} 0<k)

  p : (ℝ1/ k k-inv * ℝ1/ vl vl-inv) * (vector-length (k v* v)) == 1ℝ
  p = *-right (vector-length-* k v >=> *-left abs-k-path) >=>
      *-left *-commute >=>
      *-assoc >=> *-right (sym *-assoc >=> *-left (ℝ1/-inverse k k-inv) >=> *-left-one) >=>
      ℝ1/-inverse vl vl-inv


normalize-vector-v- :
   (v : Vector) -> (v#0 : v v# 0v) -> (-v#0 : (v- v) v# 0v) ->
   normalize-vector (v- v) -v#0 == v- (normalize-vector v v#0)
normalize-vector-v- v v#0 -v#0 =
  sym (sym v*-left-minus-one >=>
       (cong (_v* nv) (sym *-right-one >=>
                       *-right (sym (ℝ1/-inverse vl vl-inv)) >=>
                       sym *-assoc >=>
                       *-left *-commute)) >=>
       v*-assoc >=>
       cong (((ℝ1/ vl vl-inv) * (- 1ℝ)) v*_) (sym (normalize-vector-path v v#0)) >=>
       v*-assoc >=>
       cong ((ℝ1/ vl vl-inv) v*_) (v*-left-minus-one >=> normalize-vector-path -v -v#0 >=>
                                   cong (_v* n-v) (vector-length-v- v)) >=>
       sym v*-assoc >=>
       (cong (_v* n-v) (ℝ1/-inverse vl vl-inv)) >=>
       v*-left-one)
  where
  -v = v- v
  nv = (normalize-vector v v#0)
  n-v = (normalize-vector -v -v#0)
  vl = (vector-length v)
  vl-inv = (inj-r (vector-length>0 v v#0))



vector->direction : (v : Vector) -> v v# 0v -> Direction
vector->direction v v#0 = normalize-vector v v#0 , path
  where
  vl = (vector-length v)
  0<vl = (vector-length>0 v v#0)
  vl-inv = (inj-r 0<vl)
  k = (ℝ1/ vl vl-inv)
  0<1 : 0ℝ < 1ℝ
  0<1 = ℚ->ℝ-preserves-< 0r 1r 0<1r
  0≤k : 0ℝ ≤ k
  0≤k k<0 = asym-< {_} {_} {_} {0ℝ} {1ℝ} 0<1
                   (subst2 _<_ (ℝ1/-inverse vl vl-inv) (*-right-zero {m = k})
                               (*₁-flips-< k 0ℝ vl k<0 0<vl))
  path : vector-length (k v* v) == 1ℝ
  path = vector-length-* k v >=> *-left (absℝ-NonNeg-idem k 0≤k) >=> ℝ1/-inverse vl vl-inv

conjugate-preserves-vector-length² :
  (v : Vector) -> vector-length² (conjugate-vector v) == vector-length² v
conjugate-preserves-vector-length² v = +-right minus-extract-both

conjugate-preserves-vector-length :
  (v : Vector) -> vector-length (conjugate-vector v) == vector-length v
conjugate-preserves-vector-length v =
  cong2-dep sqrtℝ p (isProp->PathP (\i -> isProp-≤ 0ℝ (p i)) _ _)
  where
  p = conjugate-preserves-vector-length² v

conjugate-direction : Direction -> Direction
conjugate-direction (v , p) = conjugate-vector v , conjugate-preserves-vector-length v >=> p


xaxis-vector : Vector
xaxis-vector = direct-product-cons (\{ x-axis -> 1# ; y-axis -> 0#})
yaxis-vector : Vector
yaxis-vector = direct-product-cons (\{ x-axis -> 0# ; y-axis -> 1#})


xaxis-dir : Direction
xaxis-dir = xaxis-vector , path
  where
  abstract
    path2 : vector-length² xaxis-vector == 1#
    path2 = +-cong *-right-one *-right-zero >=> +-right-zero

    path : vector-length xaxis-vector == 1#
    path = eqFun (isUnitVector'-equiv xaxis-vector) path2

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
rotate-direction d (v , vl=1) = rotate d v , rotate-preserves-vector-length d v >=> vl=1


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

axis-basis : Axis -> Vector
axis-basis x-axis = xaxis-vector
axis-basis y-axis = yaxis-vector

isBasis-axis-basis : isBasis axis-basis
isBasis-axis-basis = subst isBasis (funExt f) (isBasis-standard-basis ℝField Axis)
  where
  s = standard-basis ℝField Axis
  g : (a1 a2 : Axis) -> (direct-product-index (s a1) a2) == (direct-product-index (axis-basis a1) a2)
  g x-axis x-axis = indicator-path (yes refl)
  g x-axis y-axis = indicator-path (no x-axis≠y-axis)
  g y-axis x-axis = indicator-path (no (x-axis≠y-axis ∘ sym))
  g y-axis y-axis = indicator-path (yes refl)

  f : (a : Axis) -> s a == axis-basis a
  f a = \i -> direct-product-cons (\a2 -> g a a2 i)


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


data SameSemiDirection : Rel Direction ℓ-one where
  same-semi-direction-same : {d1 d2 : Direction} -> ⟨ d1 ⟩ == ⟨ d2 ⟩ -> SameSemiDirection d1 d2
  same-semi-direction-flipped : {d1 d2 : Direction} -> ⟨ d1 ⟩ == (v- ⟨ d2 ⟩) -> SameSemiDirection d1 d2

sym-SameSemiDirection : {d1 d2 : Direction} -> SameSemiDirection d1 d2 -> SameSemiDirection d2 d1
sym-SameSemiDirection (same-semi-direction-same p) = same-semi-direction-same (sym p)
sym-SameSemiDirection (same-semi-direction-flipped p) =
  same-semi-direction-flipped (sym v--double-inverse >=> cong v-_ (sym p))

DifferentSemiDirection : Rel Direction ℓ-one
DifferentSemiDirection (v1 , _) (v2 , _) = (v1 v# v2) × (v1 v# (v- v2))

isProp-DifferentSemiDirection : (d1 d2 : Direction) -> isProp (DifferentSemiDirection d1 d2)
isProp-DifferentSemiDirection (v1 , _) (v2 , _) = isProp× (isProp-v# v1 v2) (isProp-v# v1 (v- v2))

DifferentSemiDirection-hProp : Direction -> Direction -> hProp ℓ-one
DifferentSemiDirection-hProp d1 d2 =
  DifferentSemiDirection d1 d2 , isProp-DifferentSemiDirection d1 d2


v--preserves-# : {v1 v2 : Vector} -> v1 # v2 -> (v- v1) # (v- v2)
v--preserves-# {v1} {v2} = ∥-map handle
  where
  handle : Σ[ a ∈ Axis ] (direct-product-index v1 a) # (direct-product-index v2 a) ->
           Σ[ a ∈ Axis ] (direct-product-index (v- v1) a) # (direct-product-index (v- v2) a)
  handle (a , cv1#cv2) = (a , minus-reflects-# cv1#cv2)

sym-DifferentSemiDirection :
  (d1 d2 : Direction) -> DifferentSemiDirection d1 d2 -> DifferentSemiDirection d2 d1
sym-DifferentSemiDirection (v1 , _) (v2 , _) (v1#v2 , v1#-v2) =
  (sym-# v1#v2 , subst (_# (v- v1)) v--double-inverse (sym-# (v--preserves-# v1#-v2)))

sym-path-DifferentSemiDirection :
  (d1 d2 : Direction) -> DifferentSemiDirection d1 d2 == DifferentSemiDirection d2 d1
sym-path-DifferentSemiDirection d1 d2 =
  ua (isoToEquiv
       (isProp->iso (sym-DifferentSemiDirection d1 d2) (sym-DifferentSemiDirection d2 d1)
                    (isProp-DifferentSemiDirection d1 d2) (isProp-DifferentSemiDirection d2 d1)))

DifferentSemiDirection-d-₂ :
  (d1 d2 : Direction) -> DifferentSemiDirection d1 d2 -> DifferentSemiDirection d1 (d- d2)
DifferentSemiDirection-d-₂ (v1 , _) (v2 , _) (v1#v2 , v1#-v2) =
  (v1#-v2 , subst (v1 #_) (sym v--double-inverse) v1#v2)

d--double-inverse : (d : Direction) -> (d- (d- d)) == d
d--double-inverse _ = ΣProp-path (\{v} -> isProp-isUnitVector v) v--double-inverse

DifferentSemiDirection-d-₂-path :
  (d1 d2 : Direction) -> DifferentSemiDirection d1 d2 == DifferentSemiDirection d1 (d- d2)
DifferentSemiDirection-d-₂-path d1 d2 =
  ua (isoToEquiv
       (isProp->iso (DifferentSemiDirection-d-₂ d1 d2) (DifferentSemiDirection-d-₂' d1 d2)
                    (isProp-DifferentSemiDirection d1 d2) (isProp-DifferentSemiDirection d1 (d- d2))))
  where
  DifferentSemiDirection-d-₂' :
    (d1 d2 : Direction) -> DifferentSemiDirection d1 (d- d2) -> DifferentSemiDirection d1 d2
  DifferentSemiDirection-d-₂' d1 d2 dsd =
    subst (DifferentSemiDirection d1) (d--double-inverse d2)
          (DifferentSemiDirection-d-₂ d1 (d- d2) dsd)



DifferentSemiDirection-d-₁ :
  (d1 d2 : Direction) -> DifferentSemiDirection d1 d2 -> DifferentSemiDirection (d- d1) d2
DifferentSemiDirection-d-₁ d1 d2 =
  sym-DifferentSemiDirection d2 (d- d1) ∘
  DifferentSemiDirection-d-₂ d2 d1 ∘
  sym-DifferentSemiDirection d1 d2

DifferentSemiDirection-d-₁-path :
  (d1 d2 : Direction) -> DifferentSemiDirection d1 d2 == DifferentSemiDirection (d- d1) d2
DifferentSemiDirection-d-₁-path d1 d2 =
  sym-path-DifferentSemiDirection d1 d2 >=>
  DifferentSemiDirection-d-₂-path d2 d1 >=>
  sym-path-DifferentSemiDirection d2 (d- d1)


DifferentSemiDirection-~₁ : (d1 d2 d3 : Direction) -> SameSemiDirection d1 d2 ->
                            DifferentSemiDirection-hProp d1 d3 == DifferentSemiDirection-hProp d2 d3
DifferentSemiDirection-~₁ d1 d2 d3 (same-semi-direction-same p) =
  cong (\d -> DifferentSemiDirection-hProp d d3) d1=d2
  where
  d1=d2 : d1 == d2
  d1=d2 = ΣProp-path (\{v} -> isProp-isUnitVector v) p
DifferentSemiDirection-~₁ d1 d2 d3 (same-semi-direction-flipped p) =
  ΣProp-path isProp-isProp dsd1=dsd2
  where
  d1=-d2 : d1 == (d- d2)
  d1=-d2 = ΣProp-path (\{v} -> isProp-isUnitVector v) p

  dsd1=dsd2 : DifferentSemiDirection d1 d3 == DifferentSemiDirection d2 d3
  dsd1=dsd2 = cong (\d -> DifferentSemiDirection d d3) d1=-d2 >=>
              sym (DifferentSemiDirection-d-₁-path d2 d3)

DifferentSemiDirection-~₂ : (d1 d2 d3 : Direction) -> SameSemiDirection d2 d3 ->
                            DifferentSemiDirection-hProp d1 d2 == DifferentSemiDirection-hProp d1 d3
DifferentSemiDirection-~₂ d1 d2 d3 (same-semi-direction-same p) =
  cong (\d -> DifferentSemiDirection-hProp d1 d) d2=d3
  where
  d2=d3 : d2 == d3
  d2=d3 = ΣProp-path (\{v} -> isProp-isUnitVector v) p
DifferentSemiDirection-~₂ d1 d2 d3 (same-semi-direction-flipped p) =
  ΣProp-path isProp-isProp dsd2=dsd3
  where
  d2=-d3 : d2 == (d- d3)
  d2=-d3 = ΣProp-path (\{v} -> isProp-isUnitVector v) p

  dsd2=dsd3 : DifferentSemiDirection d1 d2 == DifferentSemiDirection d1 d3
  dsd2=dsd3 = cong (DifferentSemiDirection d1) d2=-d3 >=>
              sym (DifferentSemiDirection-d-₂-path d1 d3)

SemiDirection = Direction / SameSemiDirection

vector->semi-direction : (v : Vector) -> v v# 0v -> SemiDirection
vector->semi-direction v v#0 = [ vector->direction v v#0 ]

vector->semi-direction-v* :
  (v : Vector) -> (v#0 : v v# 0v) -> (k : ℝ) -> (kv#0 : (k v* v) v# 0v) ->
  vector->semi-direction (k v* v) kv#0 == vector->semi-direction v v#0
vector->semi-direction-v* v v#0 k kv#0 = handle (eqInv (<>-equiv-# k 0ℝ) k#0)
  where
  k#0 = fst (v*-apart-zero kv#0)
  handle : (k ℝ# 0ℝ) -> vector->semi-direction (k v* v) kv#0 == vector->semi-direction v v#0
  handle (inj-r 0<k) = eq/ _ _ (same-semi-direction-same (normalize-vector-v*-Pos v v#0 k 0<k kv#0))
  handle (inj-l k<0) = eq/ _ _ (same-semi-direction-flipped p)
    where
    -k = - k
    0<-k = minus-flips-<0 {_} {_} {_} {_} {_} {k} k<0

    v-p1 : (v- (k v* v)) == ((- k) v* v)
    v-p1 = sym v*-minus-extract-left

    -kv#0 : ((- k) v* v) v# 0v
    -kv#0 = v*-#0 (eqFun (<>-equiv-# -k 0ℝ) (inj-r 0<-k)) v#0

    v-kv#0 : (v- (k v* v)) v# 0v
    v-kv#0 = subst (_v# 0v) (sym v-p1) -kv#0

    p1 : normalize-vector ((- k) v* v) -kv#0 == (normalize-vector v v#0)
    p1 = normalize-vector-v*-Pos v v#0 -k 0<-k -kv#0
    p2 : normalize-vector (v- (k v* v)) v-kv#0 == v- (normalize-vector (k v* v) kv#0)
    p2 = normalize-vector-v- (k v* v) kv#0 v-kv#0
    p3 : normalize-vector (v- (k v* v)) v-kv#0 == normalize-vector ((- k) v* v) -kv#0
    p3 = cong2-dep normalize-vector v-p1 (isProp->PathP (\i -> isProp-v# (v-p1 i) _) v-kv#0 -kv#0)

    p : normalize-vector (k v* v) kv#0 == v- (normalize-vector v v#0)
    p = sym v--double-inverse >=> cong v-_ (sym p2 >=> p3 >=> p1)


direction-span' : Direction -> Pred Vector ℓ-one
direction-span' (v , _) v2 = Σ[ k ∈ ℝ ] (k v* v == v2)


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


direction-span : Direction -> Subtype Vector ℓ-one
direction-span d@(v , vl=1) v2 = direction-span' d v2 , isProp-direction-span
  where
  isProp-direction-span : isProp (direction-span' d v2)
  isProp-direction-span (k1 , p1) (k2 , p2) =
    ΣProp-path (\{k} -> (isSet-DirectProduct isSet-ℝ (k v* v) v2)) k1=k2
    where
    kv-p : (k1 v* v) == (k2 v* v)
    kv-p = p1 >=> sym p2

    v#0 : v v# 0v
    v#0 = vector-length>0-#0 v (subst (0# <_) (sym vl=1) 0ℝ<1ℝ)

    handle : Σ[ a ∈ Axis ] (direct-product-index v a) # 0# -> k1 == k2
    handle (axis , c#0) = *₂-reflects-= c#0 (cong (\v -> direct-product-index v axis) kv-p)

    k1=k2 : k1 == k2
    k1=k2 = unsquash (isSet-ℝ k1 k2) (∥-map handle v#0)


direction-span'-comp : Direction -> Pred Vector ℓ-one
direction-span'-comp (dv , _) v =
  (v # ((vector-length v) v* dv)) × (v # ((vector-length v) v* (v- dv)))

-- direction-span'-comp-tight : (d : Direction) (v : Vector) ->
--                              ¬ (direction-span'-comp d v) -> direction-span' d v
-- direction-span'-comp-tight d@(dv , _) v _ = ?

direction-span-comp : Direction -> Subtype Vector ℓ-one
direction-span-comp d v = direction-span'-comp d v , isProp× isProp-# isProp-#

same-semi-direction-span : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
                           (direction-span d1) == (direction-span d2)
same-semi-direction-span d1 d2 same-semi =
  same-Subtype (handle same-semi) (handle (sym-SameSemiDirection same-semi))
  where
  handle : {d1 d2 : Direction} {v : Vector} -> SameSemiDirection d1 d2 ->
           (direction-span' d1 v) -> (direction-span' d2 v)
  handle (same-semi-direction-same p) (k , kd=v) = (k , cong (k v*_) (sym p) >=> kd=v)
  handle (same-semi-direction-flipped p) (k , kd=v) =
    ((- k) , v*-minus-extract-left >=> sym v*-minus-extract-right >=>
             cong (k v*_) (sym p) >=> kd=v)

same-semi-direction-span-comp : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
                                (direction-span-comp d1) == (direction-span-comp d2)
same-semi-direction-span-comp d1 d2 same-semi =
  same-Subtype (handle same-semi) (handle (sym-SameSemiDirection same-semi))
  where
  handle : {d1 d2 : Direction} {v : Vector} -> SameSemiDirection d1 d2 ->
           (direction-span'-comp d1 v) -> (direction-span'-comp d2 v)
  handle {v = v} (same-semi-direction-same p) (v#vldv , v#vl-dv) =
    subst (\dv -> v # (vector-length v v* dv)) p v#vldv ,
    subst (\dv -> v # (vector-length v v* (v- dv))) p v#vl-dv
  handle {v = v} (same-semi-direction-flipped p) (v#vldv , v#vl-dv) =
    subst (\dv -> v # (vector-length v v* dv)) (cong v-_ p >=> v--double-inverse) v#vl-dv ,
    subst (\dv -> v # (vector-length v v* dv)) p v#vldv

module SemiDirectionElim = SetQuotientElim Direction SameSemiDirection

semi-direction-span : SemiDirection -> Subtype Vector ℓ-one
semi-direction-span = SemiDirectionElim.rec isSet-Subtype direction-span same-semi-direction-span

semi-direction-span-comp : SemiDirection -> Subtype Vector ℓ-one
semi-direction-span-comp =
  SemiDirectionElim.rec isSet-Subtype direction-span-comp same-semi-direction-span-comp


sd#-full : SemiDirection -> SemiDirection -> hProp ℓ-one
sd#-full = SemiDirectionElim.rec2 isSet-hProp DifferentSemiDirection-hProp
                                  DifferentSemiDirection-~₁ DifferentSemiDirection-~₂

_sd#_ : Rel SemiDirection ℓ-one
_sd#_ sd1 sd2 = fst (sd#-full sd1 sd2)

isProp-sd# : (sd1 sd2 : SemiDirection) -> isProp (sd1 sd# sd2)
isProp-sd# sd1 sd2 = snd (sd#-full sd1 sd2)
