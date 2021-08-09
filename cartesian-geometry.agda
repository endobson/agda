{-# OPTIONS --cubical --safe --exact-split #-}


module cartesian-geometry where

open import base
open import equality
open import direct-product
open import functions
open import hlevel
open import isomorphism
open import real
open import relation
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.order
open import real.heyting-field
open import set-quotient
open import semiring
open import sigma
open import truncation
open import univalence
open import ring.implementations.real
open import ring
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

isUnitVector : Pred Vector ℓ-one
isUnitVector v = vector-length² v == 1ℝ

Direction : Type₁
Direction = Σ Vector isUnitVector

data SameSemiDirection : Rel Vector ℓ-one where
  same-semi-direction-same : {v1 v2 : Vector} -> v1 == v2 -> SameSemiDirection v1 v2
  same-semi-direction-flipped : {v1 v2 : Vector} -> v1 == (v- v2) -> SameSemiDirection v1 v2

SemiDirection = Direction / (\x y -> SameSemiDirection ⟨ x ⟩ ⟨ y ⟩)
