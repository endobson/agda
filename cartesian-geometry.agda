{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry where

open import additive-group
open import additive-group.instances.real
open import apartness
open import cartesian-geometry.vector
open import base
open import direct-product
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import isomorphism
open import integral-domain
open import integral-domain.instances.real
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
open import set-quotient
open import subset
open import sum
open import sigma
open import truncation
open import univalence
open import vector-space


record Point : Type₁ where
  field
    x : ℝ
    y : ℝ

P-coord : Point -> Axis -> ℝ
P-coord p x-axis = Point.x p
P-coord p y-axis = Point.y p

P-ext : {p1 p2 : Point} -> ((a : Axis) -> P-coord p1 a == P-coord p2 a) -> p1 == p2
P-ext f i = record { x = f x-axis i ; y = f y-axis i }


_P#_ : Point -> Point -> Type₁
p1 P# p2 = ∥ (p1.x ℝ# p2.x) ⊎ (p1.y ℝ# p2.y) ∥
  where
  module p1 = Point p1
  module p2 = Point p2

abstract
  isSet-Point : isSet Point
  isSet-Point = isSet-Retract point-decons point-cons (\_ -> refl) (isSet× isSet-ℝ isSet-ℝ)
    where
    point-decons : Point -> ℝ × ℝ
    point-decons p = Point.x p , Point.y p

    point-cons : ℝ × ℝ -> Point
    point-cons (x , y) = record {x = x ; y = y}


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
  { x = +-swap {_} {_} {_} {p1.x} {p2.x} {p3.x} {p4.x} i
  ; y = +-swap {_} {_} {_} {p1.y} {p2.y} {p3.y} {p4.y} i
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

P-diff-step : (p1 p2 : Point) -> P-shift p1 (P-diff p1 p2) == p2
P-diff-step p1 p2 = P-ext (\{x-axis -> diff-step ; y-axis -> diff-step})

P-shift-step : (p : Point) (v : Vector) -> P-diff p (P-shift p v) == v
P-shift-step _ _ = vector-ext (\{x-axis -> path1 ; y-axis -> path1})
  where
  path1 : {p v : ℝ} -> (diff p (p + v)) == v
  path1 = +-left +-commute >=> +-assoc >=> +-right +-inverse >=> +-right-zero

P-shift-0v : (p : Point) -> P-shift p 0v == p
P-shift-0v _ = P-ext (\{x-axis -> +-right-zero ; y-axis -> +-right-zero})


P-diff-trans : (p1 p2 p3 : Point) -> P-diff p1 p2 v+ P-diff p2 p3 == P-diff p1 p3
P-diff-trans p1 p2 p3 = vector-ext (\{x-axis -> diff-trans ; y-axis -> diff-trans})

P-diff-anticommute : (p1 p2 : Point) -> P-diff p1 p2 == v- (P-diff p2 p1)
P-diff-anticommute p1 p2 = vector-ext (\{x-axis -> diff-anticommute ; y-axis -> diff-anticommute})


-- Collinear : Point -> Point -> Point -> Type₁

record Triangle (p1 p2 p3 : Point) : Type₁ where
  field
    distinct12 : p1 P# p2
    distinct23 : p2 P# p3
    distinct31 : p3 P# p1
