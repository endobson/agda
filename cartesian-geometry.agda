{-# OPTIONS --cubical --safe --exact-split #-}


module cartesian-geometry where

open import apartness
open import base
open import direct-product
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import order
open import order.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
open import real.arithmetic
open import real.arithmetic.absolute-value
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.order
open import real.arithmetic.sqrt
open import real.arithmetic.sqrt.base
open import real.heyting-field
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import subset
open import set-quotient
open import sigma
open import truncation
open import univalence
open import vector-space


record Point : Type₁ where
  field
    x : ℝ
    y : ℝ

data Axis : Type₀ where
 x-axis : Axis
 y-axis : Axis

Vector : Type₁
Vector = DirectProduct ℝ Axis

instance
  VectorSpaceStr-Vector = VectorSpaceStr-DirectProduct ℝField Axis
  ModuleSpaceStr-Vector = VectorSpaceStr.module-str VectorSpaceStr-Vector

P-coord : Point -> Axis -> ℝ
P-coord p x-axis = Point.x p
P-coord p y-axis = Point.y p


_P#_ : Point -> Point -> Type₀
p1 P# p2 = ∥ (p1.x ℝ# p2.x) ⊎ (p1.y ℝ# p2.y) ∥
  where
  module p1 = Point p1
  module p2 = Point p2

isSet-Point : isSet Point
isSet-Point p1 p2 path1 path2 i j = record
  { x = isSet-ℝ p1.x p2.x (cong Point.x path1) (cong Point.x path2) i j
  ; y = isSet-ℝ p1.y p2.y (cong Point.y path1) (cong Point.y path2) i j
  }
  where
  module p1 = Point p1
  module p2 = Point p2

_P+_ : Point -> Point -> Point
p1 P+ p2 = record
  { x = p1.x ℝ+ p2.x
  ; y = p1.y ℝ+ p2.y
  }
  where
  module p1 = Point p1
  module p2 = Point p2


P+-swap : (p1 p2 p3 p4 : Point) -> (p1 P+ p2) P+ (p3 P+ p4) == (p1 P+ p3) P+ (p2 P+ p4)
P+-swap p1 p2 p3 p4 i = record
  { x = +-swap {_} {_} {p1.x} {p2.x} {p3.x} {p4.x} i
  ; y = +-swap {_} {_} {p1.y} {p2.y} {p3.y} {p4.y} i
  }
  where
  module p1 = Point p1
  module p2 = Point p2
  module p3 = Point p3
  module p4 = Point p4

0P : Point
0P = record { x = 0ℝ ; y = 0ℝ }

P-diff : Point -> Point -> Vector
P-diff p1 p2 = direct-product-cons (\a -> (P-coord p2 a) ℝ+ (ℝ- (P-coord p1 a)))

P-shift : Point -> Vector -> Point
P-shift p v = record
  { x = Point.x p + direct-product-index v x-axis
  ; y = Point.y p + direct-product-index v y-axis
  }

-- Collinear : Point -> Point -> Point -> Type₁

record Triangle (p1 p2 p3 : Point) : Type₁ where
  field
    distinct12 : p1 P# p2
    distinct23 : p2 P# p3
    distinct31 : p3 P# p1

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

isUnitVector : Pred Vector ℓ-one
isUnitVector v = vector-length v == 1ℝ

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

-- vector-length>0-#0 : (v : Vector) -> (vector-length v > 0#) -> (v v# 0v)
-- vector-length>0-#0 v l>0 = ?


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



data SameSemiDirection : Rel Direction ℓ-one where
  same-semi-direction-same : {d1 d2 : Direction} -> ⟨ d1 ⟩ == ⟨ d2 ⟩ -> SameSemiDirection d1 d2
  same-semi-direction-flipped : {d1 d2 : Direction} -> ⟨ d1 ⟩ == (v- ⟨ d2 ⟩) -> SameSemiDirection d1 d2

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

-- direction-span : Direction -> Subtype Vector ℓ-one
-- direction-span d@(v , _) v2 = direction-span' d v2 , isProp-direction-span
--   where
--   isProp-direction-span : isProp (direction-span' d v2)
--   isProp-direction-span (k1 , p1) (k2 , p2) = ?
--     where
--     vl-p : (k1 v* v) == (k2 v* v)
--     vl-p = cong vector-length (p1 >=> sym p2)


--semi-direction-span : SemiDirection -> Subtype Vector ℓ-one
--semi-direction-span s = ?
