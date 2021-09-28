{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.matrix where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry.vector
open import direct-product
open import equality
open import finite-commutative-monoid.instances
open import finsum
open import finsum.arithmetic
open import funext
open import heyting-field
open import hlevel
open import real
open import real.heyting-field
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import vector-space

-- Matrix : Row × Column
record Matrix : Type₁ where
  no-eta-equality
  constructor matrix
  field
    f : Axis -> Axis -> ℝ

matrix-index : Matrix -> Axis -> Axis -> ℝ
matrix-index m = Matrix.f m

matrix-ext : {m1 m2 : Matrix} -> ((a1 a2 : Axis) -> matrix-index m1 a1 a2 == matrix-index m2 a1 a2) ->
             m1 == m2
matrix-ext {matrix _} {matrix _} f i = matrix (\a1 a2 -> f a1 a2 i)

isSet-Matrix : isSet Matrix
isSet-Matrix =
  isSet-Retract Matrix.f matrix (\_ -> matrix-ext (\_ _ -> refl)) (isSetΠ2 (\_ _ -> isSet-ℝ))

private
  matrix-row : Matrix -> Axis -> (Axis -> ℝ)
  matrix-row m a a2 = matrix-index m a a2

  matrix-column : Matrix -> Axis -> (Axis -> ℝ)
  matrix-column m a a2 = matrix-index m a2 a

_mv*_ : Matrix -> Vector -> Vector
_mv*_ m v =
  direct-product-cons (\a -> (finiteSum (\a2 -> matrix-index m a a2 * (vector-index v a2))))

_m*_ : Matrix -> Matrix -> Matrix
_m*_ m1 m2 = matrix (\a1 a2 -> axis-dot-product (matrix-row m1 a1) (matrix-column m2 a2))

identity-matrix : Matrix
identity-matrix .Matrix.f x-axis x-axis = 1#
identity-matrix .Matrix.f x-axis y-axis = 0#
identity-matrix .Matrix.f y-axis x-axis = 0#
identity-matrix .Matrix.f y-axis y-axis = 1#

m*-left-identity : (m : Matrix) -> identity-matrix m* m == m
m*-left-identity m = matrix-ext f
  where
  f : (a1 a2 : Axis) -> matrix-index (identity-matrix m* m) a1 a2 == matrix-index m a1 a2
  f x-axis x-axis = +-cong *-left-one *-left-zero >=> +-right-zero
  f x-axis y-axis = +-cong *-left-one *-left-zero >=> +-right-zero
  f y-axis x-axis = +-cong *-left-zero *-left-one >=> +-left-zero
  f y-axis y-axis = +-cong *-left-zero *-left-one >=> +-left-zero

m*-right-identity : (m : Matrix) -> m m* identity-matrix == m
m*-right-identity m = matrix-ext f
  where
  f : (a1 a2 : Axis) -> matrix-index (m m* identity-matrix) a1 a2 == matrix-index m a1 a2
  f x-axis x-axis = +-cong *-right-one *-right-zero >=> +-right-zero
  f x-axis y-axis = +-cong *-right-zero *-right-one >=> +-left-zero
  f y-axis x-axis = +-cong *-right-one *-right-zero >=> +-right-zero
  f y-axis y-axis = +-cong *-right-zero *-right-one >=> +-left-zero

m*-assoc : (m1 m2 m3 : Matrix) -> (m1 m* m2) m* m3 == m1 m* (m2 m* m3)
m*-assoc m1 m2 m3 = matrix-ext f
  where
  f : (a1 a2 : Axis) -> matrix-index ((m1 m* m2) m* m3) a1 a2 == matrix-index (m1 m* (m2 m* m3)) a1 a2
  f _ _ =
    +-cong (*-distrib-+-right >=> +-cong *-assoc *-assoc)
           (*-distrib-+-right >=> +-cong *-assoc *-assoc) >=>
    +-swap >=>
    sym (+-cong *-distrib-+-left *-distrib-+-left)

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
linear-transformation->matrix {f} _ = matrix (\a1 a2 -> vector-index (f (axis-basis a2)) a1)

determinant : Matrix -> ℝ
determinant m = diff (f x-axis y-axis * f y-axis x-axis) (f x-axis x-axis * f y-axis y-axis)
  where
  f = matrix-index m

record isInvertibleMatrix (m : Matrix) : Type₁ where
  no-eta-equality
  constructor is-invertible-matrix
  field
    inv : Matrix
    left-inverse : inv m* m == identity-matrix
    right-inverse : m m* inv == identity-matrix

isProp-isInvertibleMatrix : {m : Matrix} -> isProp (isInvertibleMatrix m)
isProp-isInvertibleMatrix {m}
  (is-invertible-matrix inv1 left-inv1 right-inv1)
  (is-invertible-matrix inv2 left-inv2 right-inv2) =
    (\i -> is-invertible-matrix (p i) (left-p i) (right-p i))
    where
    p : inv1 == inv2
    p =
      sym (m*-right-identity inv1) >=>
      cong (inv1 m*_) (sym right-inv2) >=>
      sym (m*-assoc inv1 m inv2) >=>
      cong (_m* inv2) left-inv1 >=>
      m*-left-identity inv2
    left-p : PathP (\i -> p i m* m == identity-matrix) left-inv1 left-inv2
    left-p = isProp->PathP (\i -> isSet-Matrix _ _) _ _
    right-p : PathP (\i -> m m* p i == identity-matrix) right-inv1 right-inv2
    right-p = isProp->PathP (\i -> isSet-Matrix _ _) _ _

inverse-matrix : (m : Matrix) -> determinant m # 0# -> Matrix
inverse-matrix m det#0 = matrix f
  where
  xx = matrix-index m x-axis x-axis
  xy = matrix-index m x-axis y-axis
  yx = matrix-index m y-axis x-axis
  yy = matrix-index m y-axis y-axis
  det = determinant m
  1/det = ℝRing.isUnit.inv (Field.#0->isUnit ℝField det#0)

  f : Axis -> Axis -> ℝ
  f x-axis x-axis = 1/det * yy
  f x-axis y-axis = 1/det * (- xy)
  f y-axis x-axis = 1/det * (- yx)
  f y-axis y-axis = 1/det * xx

module _ (m : Matrix) (det#0 : determinant m # 0#) where
  private
    inv = inverse-matrix m det#0
    det = determinant m
    1/det = ℝRing.isUnit.inv (Field.#0->isUnit ℝField det#0)
    1/det-path = ℝRing.isUnit.path (Field.#0->isUnit ℝField det#0)

    mxx = matrix-index m x-axis x-axis
    mxy = matrix-index m x-axis y-axis
    myx = matrix-index m y-axis x-axis
    myy = matrix-index m y-axis y-axis

    inv*m=id : (inv m* m) == identity-matrix
    inv*m=id = matrix-ext f
      where
      f : (a1 a2 : Axis) -> matrix-index (inv m* m) a1 a2 == matrix-index identity-matrix a1 a2
      f x-axis x-axis = ans
        where
        ans : (1/det * myy) * mxx + (1/det * (- mxy)) * myx == 1#
        ans =
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-cong *-commute minus-extract-left) >=>
          *-commute >=>
          1/det-path
      f x-axis y-axis = ans
        where
        ans : (1/det * myy) * mxy + (1/det * (- mxy)) * myy == 0#
        ans =
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-right (*-commute >=> minus-extract-right) >=> +-inverse) >=>
          *-right-zero
      f y-axis x-axis = ans
        where
        ans : (1/det * (- myx)) * mxx + (1/det * mxx) * myx == 0#
        ans =
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-commute >=> (+-right (*-commute >=> minus-extract-right)) >=> +-inverse) >=>
          *-right-zero
      f y-axis y-axis = ans
        where
        ans : (1/det * (- myx)) * mxy + (1/det * mxx) * myy == 1#
        ans =
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-commute >=> +-right (*-commute >=> minus-extract-right)) >=>
          *-commute >=>
          1/det-path

    m*inv=id : (m m* inv) == identity-matrix
    m*inv=id = matrix-ext f
      where
      f : (a1 a2 : Axis) -> matrix-index (m m* inv ) a1 a2 == matrix-index identity-matrix a1 a2
      f x-axis x-axis = ans
        where
        ans : mxx * (1/det * myy) + mxy * (1/det * (- myx)) == 1#
        ans =
          +-cong *-commute *-commute >=>
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-cong *-commute (*-commute >=> minus-extract-right)) >=>
          *-commute >=>
          1/det-path
      f x-axis y-axis = ans
        where
        ans : mxx * (1/det * (- mxy)) + mxy * (1/det * mxx) == 0#
        ans =
          +-cong *-commute *-commute >=>
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-commute >=> +-right (*-commute >=> minus-extract-right) >=> +-inverse) >=>
          *-right-zero
      f y-axis x-axis = ans
        where
        ans : myx * (1/det * myy) + myy * (1/det * (- myx)) == 0#
        ans =
          +-cong *-commute *-commute >=>
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-right (*-commute >=> minus-extract-right) >=> +-inverse) >=>
          *-right-zero

      f y-axis y-axis = ans
        where
        ans : myx * (1/det * (- mxy)) + myy * (1/det * mxx) == 1#
        ans =
          +-cong *-commute *-commute >=>
          +-cong *-assoc *-assoc >=>
          sym *-distrib-+-left >=>
          *-right (+-commute >=> (+-right minus-extract-left)) >=>
          *-commute >=>
          1/det-path

  det#0->isInvertible : isInvertibleMatrix m
  det#0->isInvertible .isInvertibleMatrix.inv = inv
  det#0->isInvertible .isInvertibleMatrix.left-inverse = inv*m=id
  det#0->isInvertible .isInvertibleMatrix.right-inverse = m*inv=id
