{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.vector where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import commutative-monoid
open import direct-product
open import direct-product.standard-basis
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import finset
open import finset.instances.base
open import finset.instances.sum
open import functions
open import funext
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import isomorphism
open import nat.order
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import ordered-semiring.squares
open import real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.sqrt
open import real.arithmetic.sqrt.base
open import real.heyting-field
open import real.order
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import sigma.base
open import subset
open import truncation
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

private
  Axis-iso-Top⊎Top : Iso Axis (Top ⊎ Top)
  Axis-iso-Top⊎Top = iso forward backward fb bf
    where
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

  Axis<->Boolean : Iso Axis Boolean
  Axis<->Boolean .Iso.fun x-axis = true
  Axis<->Boolean .Iso.fun y-axis = false
  Axis<->Boolean .Iso.inv true  = x-axis
  Axis<->Boolean .Iso.inv false = y-axis
  Axis<->Boolean .Iso.leftInv x-axis = refl
  Axis<->Boolean .Iso.leftInv y-axis = refl
  Axis<->Boolean .Iso.rightInv true  = refl
  Axis<->Boolean .Iso.rightInv false = refl



isFinSet-Axis : isFinSet Axis
isFinSet-Axis = ∣ 2 , eq2 ∣
  where
  abstract
    eq : Axis ≃ (Top ⊎ Top)
    eq = isoToEquiv Axis-iso-Top⊎Top

    eq2 : Axis ≃ Fin 2
    eq2 = subst (Axis ≃_) (cong2 _⊎_ (sym Fin-Top) (sym Fin-Top) >=> sym (Fin-+ 1 1)) eq

instance
  FinSetStr-Axis : FinSetStr Axis
  FinSetStr-Axis = record {isFin = isFinSet-Axis}

axis-dot-product : (f1 f2 : Axis -> ℝ) -> ℝ
axis-dot-product f1 f2 = (f1 x-axis * f2 x-axis) + (f1 y-axis * f2 y-axis)

finiteMerge-Axis : {ℓ : Level} {D : Type ℓ} (CM : CommMonoid D) (f : Axis -> D) ->
                   finiteMerge CM f == (CommMonoid._∙_ CM) (f x-axis) (f y-axis)
finiteMerge-Axis CM f = finiteMerge-2elem CM Axis<->Boolean f

Vector : Type₁
Vector = DirectProduct ℝ Axis

vector-cons : (Axis -> ℝ) -> Vector
vector-cons = direct-product-cons
vector-index : Vector -> Axis -> ℝ
vector-index = direct-product-index

abstract
  vector-ext : {v1 v2 : Vector} -> ((a : Axis) -> vector-index v1 a == vector-index v2 a) -> v1 == v2
  vector-ext f i = direct-product-cons (\a -> f a i)

isSet-Vector : isSet Vector
isSet-Vector = isSet-DirectProduct isSet-ℝ

instance
  AdditiveCommMonoid-Vector : AdditiveCommMonoid Vector
  AdditiveCommMonoid-Vector = AdditiveCommMonoid-DirectProduct AdditiveCommMonoid-ℝ Axis
  AdditiveGroup-Vector : AdditiveGroup AdditiveCommMonoid-Vector
  AdditiveGroup-Vector = AdditiveGroup-DirectProduct AdditiveGroup-ℝ Axis
  VectorSpaceStr-Vector : VectorSpaceStr ℝField Vector
  VectorSpaceStr-Vector = VectorSpaceStr-DirectProduct ℝField Axis
  ModuleSpaceStr-Vector = VectorSpaceStr.module-str VectorSpaceStr-Vector
  isTightApartness-Vector# = ModuleStr.isTightApartness-v# ModuleSpaceStr-Vector
  ApartAdditiveGroup-Vector : ApartAdditiveGroup AdditiveGroup-Vector isTightApartness-Vector#
  ApartAdditiveGroup-Vector = ApartAdditiveGroup-DirectProduct ApartAdditiveGroup-ℝ Axis

abstract
  AdditiveCommMonoidʰ-vector-index :
    (a : Axis) -> AdditiveCommMonoidʰ (\v -> vector-index v a)
  AdditiveCommMonoidʰ-vector-index = CommMonoidʰ-direct-product-index _ _

conjugate-coords : (Axis -> ℝ) -> (Axis -> ℝ)
conjugate-coords c x-axis = c x-axis
conjugate-coords c y-axis = - (c y-axis)

conjugate-vector : Vector -> Vector
conjugate-vector v = vector-cons (conjugate-coords (vector-index v))

conjugate-vector-v- : (v : Vector) -> conjugate-vector (v- v) == v- (conjugate-vector v)
conjugate-vector-v- v = vector-ext (\{ x-axis -> refl ; y-axis -> refl })

conjugate-vector-double-inverse : (v : Vector) -> conjugate-vector (conjugate-vector v) == v
conjugate-vector-double-inverse v = vector-ext (\{ x-axis -> refl ; y-axis -> minus-double-inverse })

vector-length² : Vector -> ℝ
vector-length² v = axis-dot-product (vector-index v) (vector-index v)

vector-length²≮0 : (v : Vector) -> (vector-length² v ≮ 0#)
vector-length²≮0 v = +-preserves-≮0 square-≮0 square-≮0
  where
  x = (direct-product-index v x-axis)
  y = (direct-product-index v y-axis)

vector-length : Vector -> ℝ
vector-length v = sqrtℝ (vector-length² v) (vector-length²≮0 v)

vector-length≮0 : (v : Vector) -> (vector-length v ≮ 0#)
vector-length≮0 v = sqrt-0≤ (vector-length² v) (vector-length²≮0 v)

opaque
  vector-length-squared-path : (v : Vector) -> (vector-length v) * (vector-length v) == (vector-length² v)
  vector-length-squared-path v = sqrt² (vector-length² v) (vector-length²≮0 v)

isUnitVector : Pred Vector ℓ-one
isUnitVector v = vector-length v == 1#

isProp-isUnitVector : (v : Vector) -> isProp (isUnitVector v)
isProp-isUnitVector v = isSet-ℝ (vector-length v) 1#

isUnitVector' : Pred Vector ℓ-one
isUnitVector' v = vector-length² v == 1#

isProp-isUnitVector' : (v : Vector) -> isProp (isUnitVector' v)
isProp-isUnitVector' v = isSet-ℝ (vector-length² v) 1#

isUnitVector'-equiv : (v : Vector) -> isUnitVector' v ≃ isUnitVector v
isUnitVector'-equiv v =
  isoToEquiv (isProp->iso forward backward (isProp-isUnitVector' v) (isProp-isUnitVector v))
  where
  forward : isUnitVector' v -> isUnitVector v
  forward p = path
    where
    p2 = p >=> sym *-left-one

    path : vector-length v == 1#
    path = cong2-dep sqrtℝ p2 (isProp->PathP (\i -> isProp-≤)) >=>
           sqrt-square 1# >=> abs-≮0-path 0≤1

  backward : isUnitVector v -> isUnitVector' v
  backward p = sym (vector-length-squared-path v) >=> *-cong p p >=> *-left-one


Direction : Type₁
Direction = Σ Vector isUnitVector

abstract
  direction-ext : {d1 d2 : Direction} -> ⟨ d1 ⟩ == ⟨ d2 ⟩ -> d1 == d2
  direction-ext = ΣProp-path (\{v} -> isProp-isUnitVector v)

isSet-Direction : isSet Direction
isSet-Direction = isSetΣ isSet-Vector (\v -> isProp->isSet (isProp-isUnitVector v))

0<-square : (x : ℝ) -> (x # 0#) -> 0# < (x * x)
0<-square x (inj-l x<0) = subst (_< (x * x)) *-right-zero (*₁-flips-< x<0 x<0)
0<-square x (inj-r 0<x) = subst (_< (x * x)) *-right-zero (*₁-preserves-< 0<x 0<x)

opaque
  vector-length>0 : (v : Vector) -> (v v# 0v) -> (vector-length v > 0#)
  vector-length>0 v v#0 = unsquash isProp-< (∥-map handle v#0)
    where
    x : ℝ
    x = (direct-product-index v x-axis)
    y : ℝ
    y = (direct-product-index v y-axis)
    xx : ℝ
    xx = x * x
    yy : ℝ
    yy = y * y
    xxyy : ℝ
    xxyy = xx + yy

    handle-vl²>0 : (vector-length² v > 0#) -> (vector-length v > 0#)
    handle-vl²>0 = sqrt-0< (vector-length² v) (vector-length²≮0 v)


    handle : Σ[ a ∈ Axis ] (direct-product-index v a) # 0# -> (vector-length v > 0#)
    handle (x-axis , x#0) = handle-vl²>0 (trans-<-≤ 0<xx xx≤xxyy)
      where
      0<xx : 0# < xx
      0<xx = 0<-square x x#0
      0≤yy : 0# ≤ yy
      0≤yy = square-≮0
      xx≤xxyy : xx ≤ xxyy
      xx≤xxyy = subst (_≤ xxyy) +-right-zero (+₁-preserves-≤ 0≤yy)
    handle (y-axis , y#0) = handle-vl²>0 (trans-<-≤ 0<yy yy≤xxyy)
      where
      0<yy : 0# < yy
      0<yy = 0<-square y y#0
      0≤xx : 0# ≤ xx
      0≤xx = square-≮0
      yy≤xxyy : yy ≤ xxyy
      yy≤xxyy = subst (_≤ xxyy) +-left-zero (+₂-preserves-≤ 0≤xx)

  vector-length>0-#0 : (v : Vector) -> (vector-length v > 0#) -> (v v# 0v)
  vector-length>0-#0 v l>0 = unsquash isProp-v# (∥-map handle (+-reflects-#0 vl²#0))
    where
    vl : ℝ
    vl = vector-length v
    vl² : ℝ
    vl² = vector-length² v
    x : ℝ
    x = (direct-product-index v x-axis)
    y : ℝ
    y = (direct-product-index v y-axis)

    vl#0 : vl # 0#
    vl#0 = inj-r l>0
    vl²#0 : vl² # 0#
    vl²#0 = subst (_# 0#) (vector-length-squared-path v) (*-preserves-#0 vl#0 vl#0)

    handle : ((x * x) # 0#) ⊎ ((y * y) # 0#) -> v v# 0v
    handle (inj-l xx#0) = ∣ x-axis , *₁-reflects-#0 xx#0 ∣
    handle (inj-r yy#0) = ∣ y-axis , *₁-reflects-#0 yy#0 ∣

  direction-#0 : (d : Direction) -> ⟨ d ⟩ v# 0v
  direction-#0 (dv , dp) = vector-length>0-#0 dv (subst (0# <_) (sym dp) 0<1)



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

vector-length-* : (k : ℝ) (v : Vector) -> vector-length (k v* v) == (abs k) * vector-length v
vector-length-* k v = p6
  where
  l2kv = vector-length² (k v* v)
  l2v = vector-length² v
  lkv = vector-length (k v* v)
  lv = vector-length v
  aklv = (abs k * lv)
  0≤l2kv = vector-length²≮0 (k v* v)
  0≤l2v = vector-length²≮0 v
  0≤lv = vector-length≮0 v
  0≤aklv = *-preserves-0≤ abs-≮0 0≤lv

  p2 : l2v == lv * lv
  p2 = sym (sqrt² l2v 0≤l2v)
  p4 : (k * k) * (lv * lv) == aklv * aklv
  p4 = *-left abs-square >=>
       *-assoc >=> *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc
  p3 : l2kv == aklv * aklv
  p3 = vector-length²-* k v >=> *-right p2 >=> p4

  p5 : lkv == sqrtℝ (aklv * aklv) square-≮0
  p5 = cong2-dep sqrtℝ p3 (isProp->PathP (\i -> isProp-≤))

  p6 : lkv == aklv
  p6 = p5 >=> sqrt-square aklv >=> abs-≮0-path 0≤aklv

vector-length²-v- : (v : Vector) -> vector-length² (v- v) == vector-length² v
vector-length²-v- v =
  cong vector-length² -v=-1v >=>
  vector-length²-* (- 1#) v >=>
  *-left (minus-extract-both >=> *-right-one) >=>
  *-left-one
  where
  -v=-1v : (v- v) == (- 1#) v* v
  -v=-1v = sym v*-left-minus-one

vector-length-v- : (v : Vector) -> vector-length (v- v) == vector-length v
vector-length-v- v = cong2-dep sqrtℝ p (isProp->PathP (\i -> isProp-≤))
  where
  p = vector-length²-v- v

d-_ : Direction -> Direction
d-_ (v , vl=1) = v- v , a.vl-=1
  where
  module a where
    abstract
      vl-=1 : vector-length (v- v) == 1#
      vl-=1 = vector-length-v- v >=> vl=1

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
  (v : Vector) -> (v#0 : v v# 0v) -> (k : ℝ) -> (0# < k) -> (kv#0 : (k v* v) v# 0v) ->
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
  abs-k-path : abs k == k
  abs-k-path = abs-≮0-path (weaken-< 0<k)

  p : (ℝ1/ k k-inv * ℝ1/ vl vl-inv) * (vector-length (k v* v)) == 1#
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
       cong (((ℝ1/ vl vl-inv) * (- 1#)) v*_) (sym (normalize-vector-path v v#0)) >=>
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

normalize-vector-v-' :
   (v1 : Vector) -> (v1#0 : v1 v# 0v) ->
   (v2 : Vector) -> (v2#0 : v2 v# 0v) ->
   (v1 == (v- v2)) ->
   v- (normalize-vector v1 v1#0) == (normalize-vector v2 v2#0)
normalize-vector-v-' v1 v1#0 v2 v2#0 v1=-v2 =
  sym (normalize-vector-v- v1 v1#0 -v1#0) >=>
  cong2-dep normalize-vector -v1=v2 (isProp->PathPᵉ (\i -> isProp-#) -v1#0 v2#0)
  where
  -v1=v2 : (v- v1) == v2
  -v1=v2 = cong v-_ v1=-v2 >=> v--double-inverse

  -v1#0 : (v- v1) # 0v
  -v1#0 = subst (_v# 0v) (sym -v1=v2) v2#0



vector->direction : (v : Vector) -> v v# 0v -> Direction
vector->direction v v#0 = normalize-vector v v#0 , a.path
  where
  vl = (vector-length v)
  0<vl = (vector-length>0 v v#0)
  vl-inv = (inj-r 0<vl)
  k = (ℝ1/ vl vl-inv)
  module a where
    abstract
      0≤k : 0# ≤ k
      0≤k k<0 = asym-< 0<1 1<0
        where
        1<0 : 1# < 0#
        1<0 = trans-=-< (sym (ℝ1/-inverse vl vl-inv) )
               (trans-<-= (*₁-flips-< k<0 0<vl) *-right-zero)

      path : vector-length (k v* v) == 1#
      path = vector-length-* k v >=> *-left (abs-≮0-path 0≤k) >=> ℝ1/-inverse vl vl-inv

record DirectionOfVector' (v : Vector) (d : Direction) : Type₁ where
  constructor direction-of-vector-cons
  field
    k : ℝ
    0≤k : 0# ≤ k
    path : k v* v == ⟨ d ⟩

DirectionOfVector : Vector -> Type₁
DirectionOfVector v = Σ Direction (DirectionOfVector' v)

isProp-DirectionOfVector' : {v : Vector} {d : Direction} -> isProp (DirectionOfVector' v d)
isProp-DirectionOfVector' {v} {d} (direction-of-vector-cons k1 0≤k1 path1)
                                  (direction-of-vector-cons k2 0≤k2 path2) =
  (\i -> record
    { k = (k-path i)
    ; 0≤k = (0≤k-path i)
    ; path = (isProp->PathPᵉ (\j -> isSet-Vector ((k-path j) v* v) ⟨ d ⟩) path1 path2 i)
    })
  where
  d-l : vector-length ⟨ d ⟩ == 1#
  d-l = (snd d)

  k-path : k1 == k2
  k-path =
    sym *-right-one >=>
    *-right (sym d-l >=>
             cong vector-length (sym path2) >=>
             vector-length-* k2 v >=>
             *-left (abs-≮0-path 0≤k2)) >=>
    sym *-assoc >=> *-left *-commute >=> *-assoc >=>
    *-right (*-left (sym (abs-≮0-path 0≤k1)) >=>
             sym (vector-length-* k1 v) >=>
             cong vector-length path1 >=>
             d-l) >=>
    *-right-one

  0≤k-path : PathP (\i -> 0# ≤ k-path i) 0≤k1 0≤k2
  0≤k-path = (isProp->PathPᵉ (\j -> isProp-≤) 0≤k1 0≤k2)


isProp-DirectionOfVector : {v : Vector} -> isProp (DirectionOfVector v)
isProp-DirectionOfVector {v} (d1 , (direction-of-vector-cons k1 0≤k1 path1))
                             (d2 , (direction-of-vector-cons k2 0≤k2 path2)) =
  ΣProp-path isProp-DirectionOfVector' d-path
  where
  d1-l : vector-length ⟨ d1 ⟩ == 1#
  d1-l = (snd d1)
  d2-l : vector-length ⟨ d2 ⟩ == 1#
  d2-l = (snd d2)
  k-path : k1 == k2
  k-path =
    sym *-right-one >=>
    *-right (sym d2-l >=>
             cong vector-length (sym path2) >=>
             vector-length-* k2 v >=>
             *-left (abs-≮0-path 0≤k2)) >=>
    sym *-assoc >=> *-left *-commute >=> *-assoc >=>
    *-right (*-left (sym (abs-≮0-path 0≤k1)) >=>
             sym (vector-length-* k1 v) >=>
             cong vector-length path1 >=>
             d1-l) >=>
    *-right-one
  d-path : d1 == d2
  d-path = direction-ext (sym path1 >=> cong (_v* v) k-path >=> path2)

DirectionOfVector'-vector->direction :
  {v : Vector} -> (v#0 : v # 0#) -> DirectionOfVector' v (vector->direction v v#0)
DirectionOfVector'-vector->direction {v} v#0 =
  (direction-of-vector-cons
    1/vl
    (asym-< 0<1/vl)
    (cong (1/vl v*_) (normalize-vector-path v v#0) >=>
     sym v*-assoc >=>
     cong (_v* (normalize-vector v v#0)) (ℝ1/-inverse vl vl-inv) >=>
     v*-left-one))
  where
  vl = vector-length v
  0<vl = (vector-length>0 v v#0)
  vl-inv = (inj-r 0<vl)
  1/vl = (ℝ1/ vl vl-inv)

  0vl<1/vl*vl : (0# * vl) < (1/vl * vl)
  0vl<1/vl*vl = subst2 _<_ (sym *-left-zero) (sym (ℝ1/-inverse vl vl-inv)) 0<1
  0<1/vl : 0# < 1/vl
  0<1/vl = *₂-reflects-< 0vl<1/vl*vl (asym-< 0<vl)



isContr-DirectionOfVector : {v : Vector} -> v # 0v -> isContr (DirectionOfVector v)
isContr-DirectionOfVector {v} v#0 = ans , isProp-DirectionOfVector ans
  where
  ans : (DirectionOfVector v)
  ans = vector->direction v v#0 , (DirectionOfVector'-vector->direction v#0)

DirectionOfVector'-direction : {d : Direction} -> DirectionOfVector' ⟨ d ⟩ d
DirectionOfVector'-direction {d} =
  (direction-of-vector-cons 1# 0≤1 v*-left-one)


conjugate-preserves-vector-length² :
  (v : Vector) -> vector-length² (conjugate-vector v) == vector-length² v
conjugate-preserves-vector-length² v = +-right minus-extract-both

conjugate-preserves-vector-length :
  (v : Vector) -> vector-length (conjugate-vector v) == vector-length v
conjugate-preserves-vector-length v =
  cong2-dep sqrtℝ p (isProp->PathP (\i -> isProp-≤))
  where
  p = conjugate-preserves-vector-length² v

conjugate-direction : Direction -> Direction
conjugate-direction (v , p) = conjugate-vector v , vl=1'
  where
  abstract
    vl=1' : vector-length (conjugate-vector v) == 1#
    vl=1' = conjugate-preserves-vector-length v >=> p

abstract
  conjugate-direction-d- : (d : Direction) -> conjugate-direction (d- d) == d- (conjugate-direction d)
  conjugate-direction-d- d = direction-ext (conjugate-vector-v- ⟨ d ⟩)

  conjugate-direction-double-inverse : (d : Direction) -> conjugate-direction (conjugate-direction d) == d
  conjugate-direction-double-inverse d = direction-ext (conjugate-vector-double-inverse ⟨ d ⟩)

xaxis-coords : Axis -> ℝ
xaxis-coords = (\{ x-axis -> 1# ; y-axis -> 0#})
yaxis-coords : Axis -> ℝ
yaxis-coords = (\{ x-axis -> 0# ; y-axis -> 1#})

xaxis-vector : Vector
xaxis-vector = direct-product-cons xaxis-coords
yaxis-vector : Vector
yaxis-vector = direct-product-cons yaxis-coords


xaxis-dir : Direction
xaxis-dir = xaxis-vector , path
  where
  abstract
    path2 : vector-length² xaxis-vector == 1#
    path2 = +-cong *-right-one *-right-zero >=> +-right-zero

    path : vector-length xaxis-vector == 1#
    path = eqFun (isUnitVector'-equiv xaxis-vector) path2

yaxis-dir : Direction
yaxis-dir = yaxis-vector , path
  where
  abstract
    path2 : vector-length² yaxis-vector == 1#
    path2 = +-cong *-right-zero *-right-one >=> +-left-zero

    path : vector-length yaxis-vector == 1#
    path = eqFun (isUnitVector'-equiv yaxis-vector) path2

axis-basis : Axis -> Vector
axis-basis x-axis = xaxis-vector
axis-basis y-axis = yaxis-vector

private
  standard-axis-basis : Family Vector Axis
  standard-axis-basis = standard-basis ℝField Axis

  axis-basis=standard-basis : axis-basis == standard-axis-basis
  axis-basis=standard-basis = funExt (\a1 -> vector-ext (\a2 -> (sym (g a1 a2))))
    where
    s = standard-axis-basis
    g : (a1 a2 : Axis) -> (direct-product-index (s a1) a2) == (direct-product-index (axis-basis a1) a2)
    g x-axis x-axis = indicator-path (yes refl)
    g x-axis y-axis = indicator-path (no x-axis≠y-axis)
    g y-axis x-axis = indicator-path (no (x-axis≠y-axis ∘ sym))
    g y-axis y-axis = indicator-path (yes refl)

axis-basis-decomposition : {v : Vector} ->
  v == vector-sum (\a -> (vector-index v a) v* (axis-basis a))
axis-basis-decomposition {v} =
  subst (\b -> v == vector-sum (\a -> (vector-index v a) v* (b a)))
        (sym axis-basis=standard-basis)
        (standard-basis-decomposition ℝField Axis)


-- Doesn't use substitution on the spanning part so that it gets better computational behavior
isBasis-axis-basis : isBasis axis-basis
isBasis-axis-basis =
  transform-isSpanning-path (funExt f) (fst (isBasis-standard-basis ℝField Axis)) ,
  subst LinearlyIndependent (funExt f) (snd (isBasis-standard-basis ℝField Axis))
  where
  s = standard-axis-basis
  g : (a1 a2 : Axis) -> (direct-product-index (s a1) a2) == (direct-product-index (axis-basis a1) a2)
  g x-axis x-axis = indicator-path (yes refl)
  g x-axis y-axis = indicator-path (no x-axis≠y-axis)
  g y-axis x-axis = indicator-path (no (x-axis≠y-axis ∘ sym))
  g y-axis y-axis = indicator-path (yes refl)

  f : (a : Axis) -> s a == axis-basis a
  f a = \i -> direct-product-cons (\a2 -> g a a2 i)

LinearlyFree-axis-basis : LinearlyFree axis-basis
LinearlyFree-axis-basis =
  subst LinearlyFree (sym axis-basis=standard-basis) (LinearlyFree-standard-basis ℝField Axis)

v--preserves-# : {v1 v2 : Vector} -> v1 # v2 -> (v- v1) # (v- v2)
v--preserves-# {v1} {v2} = ∥-map handle
  where
  handle : Σ[ a ∈ Axis ] (direct-product-index v1 a) # (direct-product-index v2 a) ->
           Σ[ a ∈ Axis ] (direct-product-index (v- v1) a) # (direct-product-index (v- v2) a)
  handle (a , cv1#cv2) = (a , minus-preserves-# cv1#cv2)


d--double-inverse : (d : Direction) -> (d- (d- d)) == d
d--double-inverse _ = ΣProp-path (\{v} -> isProp-isUnitVector v) v--double-inverse

direction-span' : Direction -> Pred Vector ℓ-one
direction-span' (v , _) v2 = Σ[ k ∈ ℝ ] (k v* v == v2)


direction-span : Direction -> Subtype Vector ℓ-one
direction-span d@(v , vl=1) v2 = direction-span' d v2 , isProp-direction-span
  where
  isProp-direction-span : isProp (direction-span' d v2)
  isProp-direction-span (k1 , p1) (k2 , p2) =
    ΣProp-path (\{k} -> (isSet-Vector (k v* v) v2)) k1=k2
    where
    kv-p : (k1 v* v) == (k2 v* v)
    kv-p = p1 >=> sym p2

    v#0 : v v# 0v
    v#0 = vector-length>0-#0 v (subst (0# <_) (sym vl=1) 0<1)

    handle : Σ[ a ∈ Axis ] (direct-product-index v a) # 0# -> k1 == k2
    handle (axis , c#0) = *₂-reflects-= c#0 (cong (\v -> direct-product-index v axis) kv-p)

    k1=k2 : k1 == k2
    k1=k2 = unsquash (isSet-ℝ k1 k2) (∥-map handle v#0)

isLinearSubtype-direction-span : (d : Direction) -> isLinearSubtype (direction-span d)
isLinearSubtype-direction-span d = record
  { closed-under-0v = 0# , v*-left-zero
  ; closed-under-v+ = \ (k1 , p1) (k2 , p2) -> k1 + k2 , v*-distrib-+ >=> cong2 _v+_ p1 p2
  ; closed-under-v* = \ k (k2 , p) -> k * k2 , v*-assoc >=> cong (k v*_) p
  }

direction-span-self : (d : Direction) -> ⟨ direction-span d ⟨ d ⟩ ⟩
direction-span-self d = 1# , v*-left-one
