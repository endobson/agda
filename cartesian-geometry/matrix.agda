{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.matrix where

open import additive-group.instances.real
open import base
open import cartesian-geometry.vector
open import direct-product
open import equality
open import finite-commutative-monoid.instances
open import finsum
open import finsum.arithmetic
open import funext
open import real
open import ring.implementations.real
open import semiring
open import vector-space

-- Matrix : Row × Column
Matrix : Type₁
Matrix = Axis -> Axis -> ℝ

_mv*_ : Matrix -> Vector -> Vector
_mv*_ m v =
  direct-product-cons (\a -> (finiteSum (\a2 -> m a a2 * (direct-product-index v a2))))

isLinearTransformation-mv* : (m : Matrix) -> isLinearTransformation (m mv*_)
isLinearTransformation-mv* m = is-linear-transformation preserves-+ preserves-*
  where
  preserves-+ : (v1 v2 : Vector) -> m mv* (v1 v+ v2) == (m mv* v1) v+ (m mv* v2)
  preserves-+ v1 v2 = vector-ext p
    where
    p : (a : Axis) -> vector-index (m mv* (v1 v+ v2)) a ==
                      vector-index ((m mv* v1) v+ (m mv* v2)) a
    p a = cong finiteSum (funExt \a2 -> *-distrib-+-left) >=> finiteMerge-split _

  preserves-* : (k : ℝ) (v : Vector) -> m mv* (k v* v) == (k v* (m mv* v))
  preserves-* k v =
    vector-ext (\a -> cong finiteSum (funExt \a2 -> sym *-assoc >=> *-left *-commute >=> *-assoc) >=>
                      finiteSum-*)

linear-transformation->matrix : {f : Vector -> Vector} -> (isLinearTransformation f) -> Matrix
linear-transformation->matrix {f} _ a1 a2 = vector-index (f (axis-basis a2)) a1
