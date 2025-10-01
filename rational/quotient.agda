{-# OPTIONS --cubical --safe --exact-split #-}

module rational.quotient where

open import rational
open import rational.integer
open import rational.order
open import int.base
open import additive-group
open import additive-group.instances.int
open import ordered-semiring
open import order
open import order.instances.rational
open import order.instances.int
open import semiring
open import base
open import equality-path

module _ (q : ℚ) (m⁺@(m , 0<m) : ℚ⁺) where
  private
    m!=0 : m != 0#
    m!=0 = (\p -> irrefl-path-< (sym p) 0<m)

    q/m : ℚ
    q/m = q * r1/ m m!=0

  quotientℚ : ℤ
  quotientℚ = floor q/m

  remainderℚ : ℚ
  remainderℚ = fractional-part q/m * m

  0≤remainderℚ : 0# ≤ remainderℚ
  0≤remainderℚ = *-preserves-0≤ (0≤fractional-part q/m) (weaken-< 0<m)

  small-remainderℚ : remainderℚ < m
  small-remainderℚ =
    trans-<-= (*₂-preserves-< (fractional-part<1 q/m) 0<m)
              *-left-one

  quotient-remainderℚ : ℤ->ℚ quotientℚ * m + remainderℚ == q
  quotient-remainderℚ =
    sym *-distrib-+-right >=>
    *-left (fractional-part-r+ q/m) >=>
    *-assoc >=>
    *-right (r1/-inverse m m!=0) >=>
    *-right-one

  quotientℚ-preserves-0≤ : 0# ≤ q -> 0# ≤ quotientℚ
  quotientℚ-preserves-0≤ 0≤q =
    floor-preserves-0≤ (*-preserves-0≤ 0≤q (weaken-< (r1/-preserves-Pos m m!=0 0<m)))
