{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.order.increasing.preserves where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import fin
open import finset.instances
open import finsum.order
open import heyting-field.instances.real
open import nat
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.exponential-series
open import real.exponential.order.increasing.base
open import real.exponential.order.positive
open import real.exponential.plus
open import real.exponential.zero
open import real.sequence.limit.order
open import ring.implementations.real
open import semiring
open import sequence.partial-sums
open import truncation

private
  exp-abs-≤ : {x : ℝ} -> exp x ≤ exp (abs x)
  exp-abs-≤ {x} = isLimit-preserves-≤ (isLimit-exp x) (isLimit-exp (abs x)) seq≤
    where
    term≤ : (i : ℕ) -> (exp-terms x i) ≤ (exp-terms (abs x) i)
    term≤ i = *₁-preserves-≤ (weaken-< (0<1/ℕ _)) (trans-≤-= abs-≤ (abs-^ℕ-path i))

    seq≤ : (i : ℕ) -> partial-sums (exp-terms x) i ≤ partial-sums (exp-terms (abs x)) i
    seq≤ i = finiteSum-preserves-≤ (\(i , _) -> term≤ i)

  exp-<0-preserves-<' : {x : ℝ} -> x < 0# -> exp x < exp 0#
  exp-<0-preserves-<' {x} x<0 = ex<e0
    where
    0<-x : 0# < (- x)
    0<-x = minus-flips-<0 x<0

    e0<emx : exp 0# < exp (- x)
    e0<emx = exp-0≤-preserves-< refl-≤ 0<-x

    0<emx : 0# < exp (- x)
    0<emx = trans-< 0<1 (trans-=-< (sym exp0-path) e0<emx)

    ex*emx<1*emx : (exp x * exp (- x)) < (1# * exp (- x))
    ex*emx<1*emx = subst2 _<_ (cong exp (sym +-inverse) >=> exp-+-path x (- x)) (sym *-left-one) e0<emx

    ex<e0 : exp x < exp 0#
    ex<e0 = trans-<-= (*₂-reflects-< ex*emx<1*emx (asym-< 0<emx)) (sym exp0-path)


opaque
  exp-preserves-< : {x y : ℝ} -> x < y -> exp x < exp y
  exp-preserves-< {x} {y} x<y =
    unsquash isProp-< (∥-bind handle (comparison-< x 0# y x<y))
    where
    flip-e-y<e-x : (exp (- y) < exp (- x)) -> exp x < exp y
    flip-e-y<e-x e-y<e-x = ex<ey
      where
      0<exey : 0# < (exp x * exp y)
      0<exey = *-preserves-0< exp-0< exp-0<

      ex<ey : exp x < exp y
      ex<ey = subst2 _<_
        (*-assoc >=> *-right exp-minus-inverse >=> *-right-one)
        (*-left *-commute >=> *-assoc >=> *-right exp-minus-inverse >=> *-right-one)
        (*₁-preserves-< 0<exey e-y<e-x)


    handle : (x < 0# ⊎ 0# < y) -> ∥ exp x < exp y ∥
    handle (inj-r 0<y) = ∥-map handle2 (comparison-< 0# (abs x) y 0<y)
      where
      handle2 : (0# < abs x ⊎ abs x < y) -> exp x < exp y
      handle2 (inj-r ax<y) = trans-≤-< exp-abs-≤ (exp-0≤-preserves-< abs-0≤ ax<y)
      handle2 (inj-l 0<ax) = handle3 (eqInv abs-#0-eq 0<ax)
        where
        handle3 : (x < 0# ⊎ 0# < x) -> exp x < exp y
        handle3 (inj-l x<0) = trans-< (exp-<0-preserves-<' x<0)
                                      (exp-0≤-preserves-< refl-≤ 0<y)
        handle3 (inj-r 0<x) = exp-0≤-preserves-< (weaken-< 0<x) x<y
    handle (inj-l x<0) = ∥-map handle2 (comparison-< 0# (abs y) (- x) (minus-flips-<0 x<0))
      where
      handle2 : (0# < (abs y) ⊎ (abs y) < (- x)) -> exp x < exp y
      handle2 (inj-l 0<ay) = handle3 (eqInv abs-#0-eq 0<ay)
        where
        handle3 : (y < 0# ⊎ 0# < y) -> exp x < exp y
        handle3 (inj-r 0<y) = trans-< (exp-<0-preserves-<' x<0)
                                      (exp-0≤-preserves-< refl-≤ 0<y)
        handle3 (inj-l y<0) = flip-e-y<e-x e-y<e-x
          where
          e-y<e-x : exp (- y) < exp (- x)
          e-y<e-x = exp-0≤-preserves-< (weaken-< (minus-flips-<0 y<0)) (minus-flips-< x<y)
      handle2 (inj-r ay<-x) = flip-e-y<e-x e-y<e-x
        where
        e-y<e-x : exp (- y) < exp (- x)
        e-y<e-x = trans-≤-< (trans-≤-= exp-abs-≤ (cong exp abs-minus))
                            (exp-0≤-preserves-< abs-0≤ ay<-x)
