{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry.vector
open import direct-product
open import equality
open import equivalence
open import functions
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import order.instances.real
open import ordered-additive-group.instances.real
open import real
open import real.arithmetic
open import relation
open import sum
open import truncation
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


abstract
  isSet-Point : isSet Point
  isSet-Point = isSet-Retract point-decons point-cons (\_ -> refl) (isSet× isSet-ℝ isSet-ℝ)
    where
    point-decons : Point -> ℝ × ℝ
    point-decons p = Point.x p , Point.y p

    point-cons : ℝ × ℝ -> Point
    point-cons (x , y) = record {x = x ; y = y}

record _p#_ (a b : Point) : Type₁ where
  no-eta-equality ; pattern
  constructor p#-cons
  private
    module a = Point a
    module b = Point b
  field
    apart : ∥ (a.x # b.x) ⊎ (a.y # b.y) ∥

private
  isProp-p# : {p1 p2 : Point} -> isProp (p1 p# p2)
  isProp-p# (p#-cons ap1) (p#-cons ap2) i = p#-cons (squash ap1 ap2 i)

  sym-p# : Symmetric _p#_
  sym-p# (p#-cons ap) = (p#-cons (∥-map (⊎-map sym-# sym-#) ap))

  irrefl-p# : Irreflexive _p#_
  irrefl-p# (p#-cons ap) = unsquash isPropBot (∥-map (either irrefl-# irrefl-#) ap)

  comparison-p# : Comparison _p#_
  comparison-p# a b c (p#-cons ap) =
    ∥-bind (either (∥-map (⊎-map (p#-cons ∘ ∣_∣ ∘ inj-l) (p#-cons ∘ ∣_∣ ∘ inj-l)) ∘ comparison-# _ _ _)
                   (∥-map (⊎-map (p#-cons ∘ ∣_∣ ∘ inj-r) (p#-cons ∘ ∣_∣ ∘ inj-r)) ∘ comparison-# _ _ _))
            ap

  tight-p# : Tight _p#_
  tight-p# ¬p# = \i -> record {x = tight-# (¬p# ∘ p#-cons ∘ ∣_∣ ∘ inj-l) i ;
                               y = tight-# (¬p# ∘ p#-cons ∘ ∣_∣ ∘ inj-r) i }

instance
  isTightApartness-p# : isTightApartness _p#_
  isTightApartness-p# = record
    { tight-# = tight-p#
    ; irrefl-# = irrefl-p#
    ; sym-# = sym-p#
    ; comparison-# = comparison-p#
    ; isProp-# = isProp-p#
    }

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
0P = record { x = 0# ; y = 0# }

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


P-shift-twice : (p : Point) (v1 v2 : Vector) -> (P-shift (P-shift p v1) v2) == P-shift p (v1 v+ v2)
P-shift-twice _ _ _ = P-ext (\{x-axis -> +-assoc ; y-axis -> +-assoc})


P-diff-trans : (p1 p2 p3 : Point) -> P-diff p1 p2 v+ P-diff p2 p3 == P-diff p1 p3
P-diff-trans p1 p2 p3 = vector-ext (\{x-axis -> diff-trans ; y-axis -> diff-trans})

P-diff-anticommute : (p1 p2 : Point) -> P-diff p1 p2 == v- (P-diff p2 p1)
P-diff-anticommute p1 p2 = vector-ext (\{x-axis -> diff-anticommute ; y-axis -> diff-anticommute})

P-diff-self : (p : Point) -> P-diff p p == 0v
P-diff-self p = vector-ext (\{x-axis -> +-inverse ; y-axis -> +-inverse})


p#->P-diff#0 : (p1 p2 : Point) -> p1 p# p2 -> (P-diff p1 p2) # 0v
p#->P-diff#0 p1 p2 (p#-cons ap) = ∥-bind handle ap
  where
  module p1 = Point p1
  module p2 = Point p2
  handle : (p1.x # p2.x) ⊎ (p1.y # p2.y) -> (P-diff p1 p2) # 0v
  handle (inj-l x#x) = ∣ x-axis , subst2 _#_ refl +-inverse (sym-# (+₂-preserves-# x#x)) ∣
  handle (inj-r y#y) = ∣ y-axis , subst2 _#_ refl +-inverse (sym-# (+₂-preserves-# y#y)) ∣

P-diff#0->p# : (p1 p2 : Point) -> (P-diff p1 p2) # 0v -> p1 p# p2
P-diff#0->p# p1 p2 = p#-cons ∘ ∥-map handle
  where
  module p1 = Point p1
  module p2 = Point p2
  handle : Σ[ a ∈ Axis ] (vector-index (P-diff p1 p2) a # 0#) -> (p1.x # p2.x) ⊎ (p1.y # p2.y)
  handle (x-axis , d#0) = inj-l (sym-# (subst2 _#_ diff-step +-right-zero (+₁-preserves-# d#0)))
  handle (y-axis , d#0) = inj-r (sym-# (subst2 _#_ diff-step +-right-zero (+₁-preserves-# d#0)))


-- Collinear : Point -> Point -> Point -> Type₁

record Triangle (p1 p2 p3 : Point) : Type₁ where
  field
    distinct12 : p1 p# p2
    distinct23 : p2 p# p3
    distinct31 : p3 p# p1
