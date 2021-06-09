{-# OPTIONS --cubical --safe --exact-split #-}


module cartesian-geometry where

open import base
open import real
open import relation
open import real.arithmetic
open import set-quotient
open import truncation


record Point : Type₁ where
  field
    x : ℝ
    y : ℝ

_P#_ : Point -> Point -> Type₀
p1 P# p2 = ∥ (p1.x ℝ# p2.x) ⊎ (p1.y ℝ# p2.y) ∥
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

record LineSegment (p1 p2 : Point) : Type₁ where
  field
    distinct : p1 P# p2

module _ (_ℝ*_ : ℝ -> ℝ -> ℝ) where
  private
    _P*_ : ℝ -> Point -> Point
    k P* p = record
      { x = k ℝ* p.x
      ; y = k ℝ* p.y
      }
      where
      module p = Point p

    Collinear : Point -> Point -> Point -> Type₁
    Collinear p1 p2 p3 = Σ[ k ∈ ℝ ] ((k P* p1) P+ ((1ℝ ℝ+ (ℝ- k)) P* p2) == p3)

    Line' : Type₁
    Line' = Σ[ p1 ∈ Point ] Σ[ p2 ∈ Point ] (LineSegment p1 p2)

    OnLine' : Line' -> Pred Point ℓ-one
    OnLine' (p1 , p2 , _) p3 = Collinear p1 p2 p3

    SameLine' : Line' -> Line' -> Type₁
    SameLine' l (p1 , p2 , _) = OnLine' l p1 × OnLine' l p2

  Line : Type₁
  Line = Line' / SameLine'
