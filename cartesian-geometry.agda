{-# OPTIONS --cubical --safe --exact-split #-}


module cartesian-geometry where

open import base
open import equality
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
open import set-quotient
open import semiring
open import sigma
open import truncation
open import univalence
open import ring.implementations.real
open import ring


record Point : Type₁ where
  field
    x : ℝ
    y : ℝ

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

record LineSegment (p1 p2 : Point) : Type₁ where
  field
    distinct : p1 P# p2

private
  1ℝ-_ : ℝ -> ℝ
  1ℝ- x = 1ℝ ℝ+ (ℝ- x)

  1ℝ--double-inverse : {x : ℝ} -> (1ℝ- (1ℝ- x)) == x
  1ℝ--double-inverse =
    +-right ℝRing.minus-distrib-plus >=>
    sym +-assoc >=>
    +-left ℝRing.+-inverse >=>
    +-left-zero >=>
    ℝRing.minus-double-inverse

  1ℝ--distrib-ℝ+-left : {x y : ℝ} -> 1ℝ- (x ℝ+ y) == (1ℝ- x) ℝ+ (ℝ- y)
  1ℝ--distrib-ℝ+-left =
    +-right ℝRing.minus-distrib-plus >=>
    sym +-assoc

  1ℝ--distrib-ℝ+-right : {x y : ℝ} -> 1ℝ- (x ℝ+ y) == (ℝ- x) ℝ+ (1ℝ- y)
  1ℝ--distrib-ℝ+-right = cong 1ℝ-_ +-commute >=> 1ℝ--distrib-ℝ+-left >=> +-commute


  1ℝ--distrib-ℝ*-left : {x y : ℝ} -> (1ℝ- (x ℝ* y)) == (1ℝ- x) ℝ+ (x ℝ* (1ℝ- y))
  1ℝ--distrib-ℝ*-left {x} {y} =
    +-left (sym +-right-zero >=>
            +-right (sym ℝRing.+-inverse >=> +-commute) >=>
            sym +-assoc) >=>
    +-assoc >=>
    +-right (cong2 _+_ (sym *-right-one) (sym ℝRing.minus-extract-right) >=>
             sym *-distrib-+-left)


private
  _P*_ : ℝ -> Point -> Point
  k P* p = record
    { x = k ℝ* p.x
    ; y = k ℝ* p.y
    }
    where
    module p = Point p

  P*-assoc : (k1 k2 : ℝ) (p : Point) -> (k1 ℝ* k2) P* p == k1 P* (k2 P* p)
  P*-assoc k1 k2 p i = record
    { x = *-assoc {_} {_} {k1} {k2} {p.x} i
    ; y = *-assoc {_} {_} {k1} {k2} {p.y} i
    }
    where
    module p = Point p

  P*-distrib-P+-left : (k : ℝ) (p1 p2 : Point) -> k P* (p1 P+ p2) == (k P* p1) P+ (k P* p2)
  P*-distrib-P+-left k p1 p2 i = record
    { x = *-distrib-+-left {_} {_} {k} {p1.x} {p2.x} i
    ; y = *-distrib-+-left {_} {_} {k} {p1.y} {p2.y} i
    }
    where
    module p1 = Point p1
    module p2 = Point p2

  P*-distrib-P+-right : (k1 k2 : ℝ) (p : Point) -> (k1 ℝ+ k2) P* p == (k1 P* p) P+ (k2 P* p)
  P*-distrib-P+-right k1 k2 p i = record
    { x = *-distrib-+-right {_} {_} {k1} {k2} {p.x} i
    ; y = *-distrib-+-right {_} {_} {k1} {k2} {p.y} i
    }
    where
    module p = Point p


  Line' : Type₁
  Line' = Σ[ p1 ∈ Point ] Σ[ p2 ∈ Point ] (LineSegment p1 p2)

  Line'-point : Line' -> ℝ -> Point
  Line'-point (p1 , p2 , _) k = (k P* p1) P+ ((1ℝ ℝ+ (ℝ- k)) P* p2)

  linear-combo : (a b k : ℝ) -> ℝ
  linear-combo a b k = (k * a) + ((1ℝ- k) * b)

  linear-combo' : (a b k : ℝ) -> ℝ
  linear-combo' a b k = b + k * (a + (ℝ- b))


--   linear-combo-< :
--     (a b k1 k2 : ℝ) -> a > b -> (linear-combo a b k1) < (linear-combo a b k2) -> k1 < k2
--   linear-combo-< a b k1 k2 b<a combo# = ? -- k1#k2
--
--   apart-linear-combo :
--     (a b k1 k2 : ℝ) -> a ℝ# b -> (linear-combo a b k1) ℝ# (linear-combo a b k2) -> k1 ℝ# k2
--   apart-linear-combo a b k1 k2 a#b combo# = ? -- k1#k2


--  Line'-point-reflects-# :
--    (l : Line') -> (k1 k2 : ℝ) -> (Line'-point l k1 P# Line'-point l k2) -> k1 ℝ# k2
--  Line'-point-reflects-# = ?


  Injective-Line'-point : (l : Line') -> Injective (Line'-point l)
  Injective-Line'-point (l1 , l2 , ls) {k1} {k2} p1==p2 =
    (unsquash (isSet-ℝ _ _) (∥-map handle (LineSegment.distinct ls)))
    where
    module l1 = Point l1
    module l2 = Point l2

    unique-linear-combo :
      (a b : ℝ) -> a ℝ# b -> (k1 * a) + ((1ℝ- k1) * b) == (k2 * a) + ((1ℝ- k2) * b) -> k1 == k2
    unique-linear-combo a b a#b path = k1==k2
      where
      zero-path : ((k1 * a) + ((1ℝ- k1) * b)) + (ℝ- ((k2 * a) + ((1ℝ- k2) * b))) == 0ℝ
      zero-path = +-left path >=> ℝRing.+-inverse

      x = (a + (ℝ- b))
      inv-x : ℝInv x
      inv-x = ℝ#->ℝInv b a (sym-ℝ# {a} {b} a#b)

      k3 = k1 + (ℝ- k2)

      reorg-path : ((k1 * a) + ((1ℝ- k1) * b)) + (ℝ- ((k2 * a) + ((1ℝ- k2) * b))) == k3 * x
      reorg-path =
        +-right (ℝRing.minus-distrib-plus >=>
                 +-cong (sym ℝRing.minus-extract-left) (sym ℝRing.minus-extract-left)) >=>
        +-swap >=>
        +-cong (sym *-distrib-+-right) (sym *-distrib-+-right) >=>
        +-right (*-left (sym 1ℝ--distrib-ℝ+-left >=> 1ℝ--distrib-ℝ+-right >=>
                         +-right (1ℝ--double-inverse >=> sym ℝRing.minus-double-inverse) >=>
                         sym ℝRing.minus-distrib-plus) >=>
                 ℝRing.minus-extract-left >=>
                 sym ℝRing.minus-extract-right) >=>
        sym *-distrib-+-left


      zero-path2 : k3 * x == 0ℝ
      zero-path2 = sym reorg-path >=> zero-path

      zero-path3 : k3 == 0ℝ
      zero-path3 =
        sym *-right-one >=>
        *-right (sym (ℝ1/-inverse x inv-x) >=> *-commute) >=>
        sym *-assoc >=>
        *-left zero-path2 >=>
        *-left-zero

      k1==k2 : k1 == k2
      k1==k2 =
        sym +-right-zero >=>
        +-right (sym (ℝ+-inverse k2) >=> +-commute) >=>
        sym +-assoc >=>
        +-left zero-path3 >=>
        +-left-zero

    handle : (l1.x ℝ# l2.x) ⊎ (l1.y ℝ# l2.y) -> k1 == k2
    handle (inj-l dx) = unique-linear-combo l1.x l2.x dx (cong Point.x p1==p2)
    handle (inj-r dy) = unique-linear-combo l1.y l2.y dy (cong Point.y p1==p2)



  OnLine' : Line' -> Pred Point ℓ-one
  OnLine' l p = Σ[ k ∈ ℝ ] (Line'-point l k == p)

  OffLine' : Line' -> Pred Point ℓ-one
  OffLine' l p = ∀ (k : ℝ) -> (Line'-point l k) P# p

  SameLine' : Line' -> Line' -> Type₁
  SameLine' l (p1 , p2 , _) = OnLine' l p1 × OnLine' l p2

  Collinear' : Point -> Point -> Point -> Type₁
  Collinear' p1 p2 p3 = ∃[ l ∈ Line' ] (OnLine' l p1 × OnLine' l p2 × OnLine' l p3)

  isProp-Collinear' : (p1 p2 p3 : Point) -> isProp (Collinear' p1 p2 p3)
  isProp-Collinear' _ _ _ = squash

  isProp-OnLine' : (l : Line') -> (p : Point) -> isProp (OnLine' l p)
  isProp-OnLine' l p (_ , path1) (_ , path2) =
    ΣProp-path (isSet-Point _ _) (Injective-Line'-point l (path1 >=> sym path2))


Line : Type₁
Line = Line' / SameLine'

module LineElim = SetQuotientElim Line' SameLine'


-- private
--  sym-SameLine' : Symmetric SameLine'
--  sym-SameLine' {l1@(l1a , l1b , l1s)} {l2@(l2a , l2b , l2s)}
--                ((c , c-path) , (d , d-path)) =  l1a∈l2 , l1b∈l2
--    where
--    l1a∈l2 : OnLine' l2 l1a
--    l1a∈l2 = ?
--    l1b∈l2 : OnLine' l2 l1b
--    l1b∈l2 = ?
--
--    c#d : c ℝ# d
--    c#d = ?
--
--    s = c + (ℝ- d)
--    inv-s : ℝInv s
--    inv-s = ℝ#->ℝInv d c (sym-ℝ# {c} {d} c#d)
--    s' = ℝ1/ s inv-s
--
--    k0 = (ℝ- d) * s'
--    k1 = (1ℝ + (ℝ- d)) * s'


module _
  (sym-SameLine' : Symmetric SameLine')
  where
  private
    reparam-OnLine' : (a b : Line') (p : Point) -> SameLine' b a
                      -> OnLine' a p -> OnLine' b p
    reparam-OnLine' a b p ((k1 , path1) , (k2 , path2)) (k3 , path3) = k4 , path4
      where
      a1 = fst a
      a2 = fst (snd a)
      b1 = fst b
      b2 = fst (snd b)

      k1' = 1ℝ- k1
      k2' = 1ℝ- k2
      k3' = 1ℝ- k3

      k4 : ℝ
      k4 = (k3 ℝ* k1) ℝ+ (k3' ℝ* k2)
      k4' = 1ℝ- k4

      k-path : k4' == (k3 ℝ* k1') ℝ+ (k3' ℝ* k2')
      k-path =
        1ℝ--distrib-ℝ+-left >=>
        cong2 _ℝ+_
             (1ℝ--distrib-ℝ*-left >=> ℝ+-commute _ _)
             -- (ℝ*-extract--- (cong (k3' ℝ*_) (sym 1ℝ--double-inverse))
             (sym ℝRing.minus-extract-right)
             >=>
        ℝ+-assoc _ _ _ >=>
        cong ((k3 ℝ* k1') ℝ+_) (+-left (sym *-right-one) >=>
                                (sym *-distrib-+-left))

      distrib-path : (k4 P* b1) P+ (k4' P* b2) ==
                     (k3  P* ((k1 P* b1) P+ (k1' P* b2))) P+
                     (k3' P* ((k2 P* b1) P+ (k2' P* b2)))
      distrib-path =
        cong ((k4 P* b1) P+_) (cong (_P* b2) k-path) >=>
        cong2 _P+_ (P*-distrib-P+-right (k3 ℝ* k1)  (k3' ℝ* k2) b1)
                   (P*-distrib-P+-right (k3 ℝ* k1') (k3' ℝ* k2') b2) >=>
        cong2 _P+_ (cong2 _P+_ (P*-assoc k3 k1  b1) (P*-assoc k3' k2  b1))
                   (cong2 _P+_ (P*-assoc k3 k1' b2) (P*-assoc k3' k2' b2)) >=>
        (P+-swap (k3 P* (k1  P* b1)) (k3' P* (k2  P* b1))
                 (k3 P* (k1' P* b2)) (k3' P* (k2' P* b2))) >=>
        cong2 _P+_
          (sym (P*-distrib-P+-left k3  (k1 P* b1) (k1' P* b2)))
          (sym (P*-distrib-P+-left k3' (k2 P* b1) (k2' P* b2)))


      path4 : (k4 P* b1) P+ ((1ℝ ℝ+ (ℝ- k4)) P* b2) == p
      path4 =
        distrib-path >=>
        (cong2 _P+_ (cong (k3 P*_) path1) (cong (k3' P*_) path2)) >=>
        path3


  OnLine-full : Line -> Point -> hProp ℓ-one
  OnLine-full l p = LineElim.elim (\_ -> isSet-hProp) val preserved l
    where
    val : Line' -> hProp ℓ-one
    val l = (OnLine' l p , isProp-OnLine' l p)
    preserved : (a b : Line') -> (SameLine' a b) -> val a == val b
    preserved a b a~b = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (⟨ val a ⟩) (⟨ val b ⟩)
      i .fun pa = reparam-OnLine' a b p (sym-SameLine' {a} {b} a~b) pa
      i .inv pb = reparam-OnLine' b a p a~b pb
      i .rightInv _ = isProp-OnLine' b p _ _
      i .leftInv _ = isProp-OnLine' a p _ _




-- Collinear : Point -> Point -> Point -> Type₁

record Triangle (p1 p2 p3 : Point) : Type₁ where
  field
    distinct12 : p1 P# p2
    distinct23 : p2 P# p3
    distinct31 : p3 P# p1
