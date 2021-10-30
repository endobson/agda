{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.matrix where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry.vector
open import cubical using (isEquiv)
open import direct-product
open import equality
open import equivalence
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finsum
open import finsum.arithmetic
open import functions
open import funext
open import heyting-field
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import real
open import real.heyting-field
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import subset
open import truncation
open import vector-space

-- Matrix : Row × Column
record Matrix : Type₁ where
  no-eta-equality ; pattern
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

matrix-transpose : Matrix -> Matrix
matrix-transpose m = matrix (\a1 a2 -> matrix-index m a2 a1)

_mv*_ : Matrix -> Vector -> Vector
_mv*_ m v =
  vector-cons (\a -> (finiteSum (\a2 -> matrix-index m a a2 * (vector-index v a2))))

_m*_ : Matrix -> Matrix -> Matrix
_m*_ m1 m2 = matrix (\a1 a2 -> axis-dot-product (matrix-row m1 a1) (matrix-column m2 a2))

matrix-mv*-ext : {m1 m2 : Matrix} -> ((v : Vector) -> m1 mv* v == m2 mv* v) -> m1 == m2
matrix-mv*-ext {m1} {m2} vp = matrix-ext f
  where

  m-path : (m : Matrix) (a1 a2 : Axis) ->
    matrix-index m a1 a2 == vector-index (m mv* (axis-basis a2)) a1
  m-path m _ x-axis =
    sym (axis-merge _ >=> +-cong *-right-one *-right-zero >=> +-right-zero)
  m-path m _ y-axis =
    sym (axis-merge _ >=> +-cong *-right-zero *-right-one >=> +-left-zero)


  f : (a1 a2 : Axis) -> (matrix-index m1 a1 a2 == matrix-index m2 a1 a2)
  f a1 a2 =
    m-path m1 a1 a2 >=>
    cong (\v -> vector-index v a1) (vp (axis-basis a2)) >=>
    sym (m-path m2 a1 a2)

identity-matrix : Matrix
identity-matrix = matrix f
  where
  f : Axis -> Axis -> ℝ
  f x-axis x-axis = 1#
  f x-axis y-axis = 0#
  f y-axis x-axis = 0#
  f y-axis y-axis = 1#

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

mv*-left-identity : (v : Vector) -> identity-matrix mv* v == v
mv*-left-identity v = vector-ext f
  where
  f : (a : Axis) -> vector-index (identity-matrix mv* v) a == vector-index v a
  f x-axis = finiteMerge-Axis _ _ >=> +-cong *-left-one *-left-zero >=> +-right-zero
  f y-axis = finiteMerge-Axis _ _ >=> +-cong *-left-zero *-left-one >=> +-left-zero


m*-assoc : (m1 m2 m3 : Matrix) -> (m1 m* m2) m* m3 == m1 m* (m2 m* m3)
m*-assoc m1 m2 m3 = matrix-ext f
  where
  f : (a1 a2 : Axis) -> matrix-index ((m1 m* m2) m* m3) a1 a2 == matrix-index (m1 m* (m2 m* m3)) a1 a2
  f _ _ =
    +-cong (*-distrib-+-right >=> +-cong *-assoc *-assoc)
           (*-distrib-+-right >=> +-cong *-assoc *-assoc) >=>
    +-swap >=>
    sym (+-cong *-distrib-+-left *-distrib-+-left)

mv*-assoc : (m1 m2 : Matrix) (v : Vector) -> (m1 m* m2) mv* v == m1 mv* (m2 mv* v)
mv*-assoc m1 m2 v = vector-ext f
  where
  f : (a : Axis) -> vector-index ((m1 m* m2) mv* v) a == vector-index (m1 mv* (m2 mv* v)) a
  f a =
    finiteMerge-Axis _ _ >=>
    +-cong *-distrib-+-right *-distrib-+-right >=>
    +-swap >=>
    +-cong (+-cong *-assoc *-assoc >=> (sym *-distrib-+-left))
           (+-cong *-assoc *-assoc >=> (sym *-distrib-+-left)) >=>
    +-cong (*-right (sym (finiteMerge-Axis _ _)))
           (*-right (sym (finiteMerge-Axis _ _))) >=>
    sym (finiteMerge-Axis _ _)

mv*-right-zero : (m : Matrix) -> m mv* 0v == 0v
mv*-right-zero m = vector-ext f
  where
  f : (a : Axis) -> vector-index (m mv* 0v) a == 0#
  f a = finiteMerge-Axis _ _ >=> +-cong *-right-zero *-right-zero >=> +-right-zero

mv*-reflects-#0 : (m : Matrix) (v : Vector) -> (m mv* v) # 0v -> v # 0v
mv*-reflects-#0 m v = ∥-bind handle
  where
  handle : Σ[ a1 ∈ Axis ] (vector-index (m mv* v) a1 # 0#) -> v # 0v
  handle (a1 , mva#0) = ∥-bind handle2 (finiteSum-#0 mva#0)
    where
    handle2 : Σ[ a2 ∈ Axis ] ((matrix-index m a1 a2 * vector-index v a2) # 0#) -> v # 0v
    handle2 (a2 , mv#0) = ∣ (a2 , *₁-reflects-#0 mv#0) ∣

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

linear-transformation->matrix-path : {f : Vector -> Vector} (lt : isLinearTransformation f) ->
  (linear-transformation->matrix lt mv*_) == f
linear-transformation->matrix-path {f} lt = funExt (\v -> vector-ext (\a -> p v a))
  where
  p : (v : Vector) (a : Axis) ->
      (vector-index (linear-transformation->matrix lt mv* v) a) == (vector-index (f v) a)
  p v a = m-path >=> cong (\v -> vector-index v a) (sym fv-path)
    where
    v-path : v == vector-sum (\a -> (vector-index v a) v* (axis-basis a))
    v-path = axis-basis-decomposition
    fv-path : f v == vector-sum (\a -> (vector-index v a) v* (f (axis-basis a)))
    fv-path =
      cong f v-path >=>
      (lt-preserves-vector-sum lt) >=>
      cong vector-sum (funExt (\a -> lt-preserves-* lt _ _))

    m-path : (vector-index (linear-transformation->matrix lt mv* v) a) ==
             (vector-index (vector-sum (\a2 -> (vector-index v a2) v* (f (axis-basis a2)))) a)
    m-path = cong finiteSum (funExt (\a2 -> *-commute)) >=>
             (finiteMerge-homo-inject _ _ (AdditiveCommMonoidʰ-vector-index a))


determinant : Matrix -> ℝ
determinant m = diff (f x-axis y-axis * f y-axis x-axis) (f x-axis x-axis * f y-axis y-axis)
  where
  f = matrix-index m

record isInvertibleMatrix (m : Matrix) : Type₁ where
  no-eta-equality ; pattern
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
  det#0->isInvertible = is-invertible-matrix inv inv*m=id m*inv=id

MatrixKernel : Matrix -> Subtype Vector ℓ-one
MatrixKernel m v = (m mv* v == 0v) , isSet-Vector _ _

0∈MatrixKernel : (m : Matrix) -> ⟨ MatrixKernel m 0v ⟩
0∈MatrixKernel m = mv*-right-zero m

isInvertible->isSingleton-MatrixKernel : {m : Matrix} ->
  isInvertibleMatrix m -> isSingletonSubtype (MatrixKernel m)
isInvertible->isSingleton-MatrixKernel {m} inv-m =
  (0v , 0∈MatrixKernel m) , isProp-ker _
  where
  module inv-m = isInvertibleMatrix inv-m
  isProp-ker : isProp (∈-Subtype (MatrixKernel m))
  isProp-ker (v1 , mv1=0) (v2 , mv2=0) = ∈-Subtype-ext (MatrixKernel m) v1=v2
    where
    v1=v2 : v1 == v2
    v1=v2 =
      sym (mv*-left-identity v1) >=>
      cong (_mv* v1) (sym inv-m.left-inverse) >=>
      mv*-assoc inv-m.inv m v1 >=>
      cong (inv-m.inv mv*_) (mv1=0 >=> sym mv2=0) >=>
      sym (mv*-assoc inv-m.inv m v2) >=>
      cong (_mv* v2) (inv-m.left-inverse) >=>
      (mv*-left-identity v2)

isInvertible->mv*-preserves-#0 : {m : Matrix} ->
  isInvertibleMatrix m -> {v : Vector} -> v # 0v ->
  (m mv* v) # 0v
isInvertible->mv*-preserves-#0 {m} inv-m {v} v#0 =
  mv*-reflects-#0 i (m mv* v) (subst (_# 0v) p v#0)
  where
  i = isInvertibleMatrix.inv inv-m
  i-path = isInvertibleMatrix.left-inverse inv-m
  p = sym (mv*-left-identity v) >=>
      cong (_mv* v) (sym i-path) >=>
      mv*-assoc i m v

isInvertible->mv*-preserves-# : {m : Matrix} ->
  isInvertibleMatrix m -> {v1 v2 : Vector} -> v1 # v2 ->
  (m mv* v1) # (m mv* v2)
isInvertible->mv*-preserves-# {m} inv-m {v1} {v2} v1#v2 =
  subst2 _#_ p +-left-zero (+₂-preserves-# mdiff#0)
  where
  diff#0 = subst2 _#_ refl +-inverse (+₂-preserves-# v1#v2)
  mdiff#0 = isInvertible->mv*-preserves-#0 inv-m diff#0
  p : (m mv* (diff v2 v1)) + (m mv* v2) == m mv* v1
  p = sym (lt-preserves-+ (isLinearTransformation-mv* m) _ _) >=>
      cong (m mv*_) (+-commute >=> diff-step)

isInvertible-linear-transformation->matrix :
  {f : Vector -> Vector} -> (lt : isLinearTransformation f) -> isEquiv f ->
  isInvertibleMatrix (linear-transformation->matrix lt)
isInvertible-linear-transformation->matrix {f} lt eq = record
  { inv = mg
  ; left-inverse = left-inverse
  ; right-inverse = right-inverse
  }
  where
  g : Vector -> Vector
  g = isEqInv eq

  g-preserves-+ : (v1 v2 : Vector) -> g (v1 + v2) == g v1 + g v2
  g-preserves-+ v1 v2 =
    cong g (+-cong (sym (isEqSec eq v1)) (sym (isEqSec eq v2)) >=>
            sym (lt-preserves-+ lt (g v1) (g v2))) >=>
    isEqRet eq _

  g-preserves-* : (k : ℝ) (v : Vector) -> g (k v* v) == k v* (g v)
  g-preserves-* k v =
    cong g (v*-right (sym (isEqSec eq v)) >=>
            sym (lt-preserves-* lt k (g v))) >=>
    isEqRet eq _

  lt2 : isLinearTransformation g
  lt2 = record {preserves-+ = g-preserves-+ ; preserves-* = g-preserves-*}

  mf = linear-transformation->matrix lt
  mg = linear-transformation->matrix lt2

  left-inverse : mg m* mf == identity-matrix
  left-inverse = matrix-mv*-ext (\v ->
    mv*-assoc mg mf v >=>
    cong2 (\g f -> g (f v))
      (linear-transformation->matrix-path lt2)
      (linear-transformation->matrix-path lt) >=>
    isEqRet eq _ >=>
    sym (mv*-left-identity v))

  right-inverse : mf m* mg == identity-matrix
  right-inverse = matrix-mv*-ext (\v ->
    mv*-assoc mf mg v >=>
    cong2 (\f g -> f (g v))
      (linear-transformation->matrix-path lt)
      (linear-transformation->matrix-path lt2) >=>
    isEqSec eq _ >=>
    sym (mv*-left-identity v))


vector-lt-preserves-# :
  {f : Vector -> Vector} -> (lt : isLinearTransformation f) -> isEquiv f ->
  {v1 v2 : Vector} -> v1 # v2 -> f v1 # f v2
vector-lt-preserves-# {f} lt eq =
  subst (\f -> {v1 v2 : Vector} -> v1 # v2 -> (f v1 # f v2))
    (linear-transformation->matrix-path lt)
    (isInvertible->mv*-preserves-# (isInvertible-linear-transformation->matrix lt eq))
