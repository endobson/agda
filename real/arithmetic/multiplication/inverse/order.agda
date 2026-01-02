{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication.inverse.order where

open import additive-group
open import additive-group.instances.real
open import equality-path
open import order
open import order.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import real.arithmetic.multiplication.inverse
open import real.subspace
open import ring.implementations.real
open import semiring
open import subset.subspace


opaque
  ℝ1/-reflects-0< : {x∈@(x , _) : ℝ# 0#} -> 0# < (ℝ1/ x∈) -> 0# < x
  ℝ1/-reflects-0< 0<1/x =
    trans-<-= (ℝ1/-preserves-0< 0<1/x) ℝ1/-double-inverse

  ℝ1/-reflects-<0 : {x∈@(x , _) : ℝ# 0#} -> (ℝ1/ x∈) < 0# -> (x < 0#)
  ℝ1/-reflects-<0 1/x<0 =
    trans-=-< (sym ℝ1/-double-inverse) (ℝ1/-preserves-<0 1/x<0)


opaque
  ℝ1/⁺-flips-< : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> 0# < x -> x < y -> ℝ1/ y∈ < ℝ1/ x∈
  ℝ1/⁺-flips-< {x∈@(x , x#0)} {y∈@(y , y#0)} 0<x x<y =
    subst2 _<_
      (*-left *-commute >=> *-assoc >=> *-right ℝ1/-inverse >=> *-right-one)
      (*-assoc >=> *-right ℝ1/-inverse >=> *-right-one)
      (*₁-preserves-< (*-preserves-0< 0<1/x 0<1/y) x<y)
    where
    0<y : 0# < y
    0<y = trans-< 0<x x<y

    0<1/x : 0# < ℝ1/ x∈
    0<1/x = ℝ1/-preserves-0< 0<x
    0<1/y : 0# < ℝ1/ y∈
    0<1/y = ℝ1/-preserves-0< 0<y

  ℝ1/⁺-flip-reflects-< : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> 0# < ℝ1/ x∈ -> ℝ1/ x∈ < ℝ1/ y∈ -> y < x
  ℝ1/⁺-flip-reflects-< 0<1/x 1/x<1/y =
    subst2 _<_ ℝ1/-double-inverse ℝ1/-double-inverse (ℝ1/⁺-flips-< 0<1/x 1/x<1/y)

  ℝ1/⁺-flips-≤ : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> 0# < x -> x ≤ y -> ℝ1/ y∈ ≤ ℝ1/ x∈
  ℝ1/⁺-flips-≤ 0<x x≤y 1/x<1/y = x≤y (ℝ1/⁺-flip-reflects-< (ℝ1/-preserves-0< 0<x) 1/x<1/y)

  ℝ1/⁺-flip-reflects-≤ : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> 0# < ℝ1/ x∈ -> ℝ1/ x∈ ≤ ℝ1/ y∈ -> y ≤ x
  ℝ1/⁺-flip-reflects-≤ 0<1/x 1/x≤1/y x<y = 1/x≤1/y (ℝ1/⁺-flips-< (ℝ1/-reflects-0< 0<1/x) x<y)


  ℝ1/⁻-flips-< : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> y < 0# -> x < y -> ℝ1/ y∈ < ℝ1/ x∈
  ℝ1/⁻-flips-< {x∈@(x , x#0)} {y∈@(y , y#0)} y<0 x<y =
    subst2 _<_
      (*-left *-commute >=> *-assoc >=> *-right ℝ1/-inverse >=> *-right-one)
      (*-assoc >=> *-right ℝ1/-inverse >=> *-right-one)
      (*₁-preserves-< (*-flips-<0 1/x<0 1/y<0) x<y)

    where
    x<0 : x < 0#
    x<0 = trans-< x<y y<0

    1/x<0 : ℝ1/ x∈ < 0#
    1/x<0 = ℝ1/-preserves-<0 x<0
    1/y<0 : ℝ1/ y∈ < 0#
    1/y<0 = ℝ1/-preserves-<0 y<0

  ℝ1/⁻-flip-reflects-< : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> ℝ1/ y∈ < 0# -> ℝ1/ x∈ < ℝ1/ y∈ -> y < x
  ℝ1/⁻-flip-reflects-< {x∈@(x , x#0)} {y∈@(y , y#0)} 1/y<0 1/x<1/y =
    subst2 _<_ ℝ1/-double-inverse ℝ1/-double-inverse (ℝ1/⁻-flips-< 1/y<0 1/x<1/y)


  ℝ1/⁻-flips-≤ : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> y < 0# -> x ≤ y -> ℝ1/ y∈ ≤ ℝ1/ x∈
  ℝ1/⁻-flips-≤ y<0 x≤y 1/x<1/y = x≤y (ℝ1/⁻-flip-reflects-< (ℝ1/-preserves-<0 y<0) 1/x<1/y)

  ℝ1/⁻-flip-reflects-≤ : {x∈@(x , _) y∈@(y , _) : ℝ# 0#} -> y < 0# -> ℝ1/ x∈ ≤ ℝ1/ y∈ -> y ≤ x
  ℝ1/⁻-flip-reflects-≤ y<0 1/x≤1/y x<y = 1/x≤1/y (ℝ1/⁻-flips-< y<0 x<y)
