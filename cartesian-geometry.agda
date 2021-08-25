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
open import real
open import real.arithmetic
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


data SameSemiDirection : Rel Vector ℓ-one where
  same-semi-direction-same : {v1 v2 : Vector} -> v1 == v2 -> SameSemiDirection v1 v2
  same-semi-direction-flipped : {v1 v2 : Vector} -> v1 == (v- v2) -> SameSemiDirection v1 v2

SemiDirection = Direction / (\x y -> SameSemiDirection ⟨ x ⟩ ⟨ y ⟩)
