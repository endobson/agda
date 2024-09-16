{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.order.increasing.reflects where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import heyting-field.instances.real
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-field.mean
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.exponential-series
open import real.exponential.bounds
open import real.exponential.order.increasing.preserves
open import real.exponential.order.positive
open import real.exponential.plus
open import ring.implementations.real
open import semiring
open import truncation

private
  exp-1<-implies-0< : {x : ℝ} -> 1# < exp x -> 0# < x
  exp-1<-implies-0< {x} 1<ex = unsquash isProp-< (∥-map handle (comparison-< _ x _ 0<ε2))
    where
    m : ℝ
    m = mean 1# (exp x)
    ε : ℝ
    ε = diff 1# m
    0<ε : 0# < ε
    0<ε = diff-0<⁺ (mean-<₁ 1<ex)

    ε/2 : ℝ
    ε/2 = ε * 1/2
    0<ε/2 : 0# < ε/2
    0<ε/2 = *-preserves-0< 0<ε 0<1/2

    ε2 : ℝ
    ε2 = min 1/2 (ε * 1/2)
    0<ε2 : 0# < ε2
    0<ε2 = min-greatest-< 0<1/2 0<ε/2

    ε2<1 : ε2 < 1#
    ε2<1 = trans-≤-< min-≤-left 1/2<1

    1+ε<ex : (1# + ε) < exp x
    1+ε<ex = trans-=-< diff-step (mean-<₂ 1<ex)

    ¬x<ε2 : ¬ (x < ε2)
    ¬x<ε2 x<ε2 = asym-< 1+ε<ex (trans-<-≤ ex<eε2 eε2≤1+ε)
      where
      eε2≤1+ε : exp ε2 ≤ (1# + ε)
      eε2≤1+ε =
        trans-≤-= (trans-≤ (exp-0≤-≤1+2x (weaken-< 0<ε2) ε2<1)
                           (+₁-preserves-≤ (*₁-preserves-≤ (weaken-< 0<2) min-≤-right)))
          (+-right (*-right *-commute >=> sym *-assoc >=> *-left 2*1/2-path >=> *-left-one))

      ex<eε2 : exp x < exp ε2
      ex<eε2 = exp-preserves-< x<ε2

    handle : (0# < x) ⊎ (x < ε2) -> 0# < x
    handle (inj-l 0<x) = 0<x
    handle (inj-r x<ε2) = bot-elim (¬x<ε2 x<ε2)

opaque
  exp-reflects-< : {x y : ℝ} -> exp x < exp y -> x < y
  exp-reflects-< {x} {y} ex<ey = diff-0<⁻ (exp-1<-implies-0< 1<e[dxy])
    where
    1<e[dxy] : 1# < exp (diff x y)
    1<e[dxy] = subst2 _<_ exp-minus-inverse (sym (exp-+-path y (- x)))
                (*₂-preserves-< ex<ey exp-0<)
