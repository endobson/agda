{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.vector where

open import apartness
open import base
open import direct-product
open import equality
open import equivalence
open import functions
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
open import truncation
open import univalence
open import vector-space


data Axis : Type₀ where
 x-axis : Axis
 y-axis : Axis

Vector : Type₁
Vector = DirectProduct ℝ Axis

instance
  VectorSpaceStr-Vector = VectorSpaceStr-DirectProduct ℝField Axis
  ModuleSpaceStr-Vector = VectorSpaceStr.module-str VectorSpaceStr-Vector
  TightApartnessStr-Vector = ModuleStr.TightApartnessStr-V ModuleSpaceStr-Vector

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