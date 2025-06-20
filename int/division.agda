{-# OPTIONS --cubical --safe --exact-split #-}

module int.division where

open import abs
open import order
open import order.instances.int
open import order.instances.nat
open import base
open import equality-path
open import int
open import nat
open import nat.division
open import ring.division
open import ring.implementations.int
open import semiring
open import truncation
open import semiring.division
open import semiring.instances.nat
open import additive-group.instances.int

-- TODO make these not over the Σ verisions

divℕ->divℤ : {d n : ℕ} -> d div' n -> (int d) div' (int n)
divℕ->divℤ {d} (x , pr) =
  (int x) , (sym (int-inject-*' {x} {d}) >=> (cong int pr))

divℤ->divℕ : {d n : ℤ} -> d div' n -> (abs' d) div' (abs' n)
divℤ->divℕ {d} (x , pr) =
  (abs' x) , (sym (abs'-inject-* {x} {d}) >=> (cong abs' pr))


private
  divℤ'-zero->zero : {n : Int} -> (int 0) div' n -> n == (int 0)
  divℤ'-zero->zero (d , pr) = (sym pr) >=> *-right-zero

divℤ-zero->zero : {n : Int} -> (int 0) div n -> n == (int 0)
divℤ-zero->zero 0%n = unsquash (isSetInt _ _) (∥-map divℤ'-zero->zero 0%n)


-- TODO make cleaner
divℤ->≤ : {d a : Int} -> d div a -> {Pos a} -> abs' d ≤ abs' a
divℤ->≤ {a = pos _} da = nat.division.div->≤ (∥-map divℤ->divℕ da) _


div-abs-right : {d a : ℤ} -> d div a -> d div (abs a)
div-abs-right {d} {zero-int} div-a = div-a
div-abs-right {d} {pos _}    div-a = div-a
div-abs-right {d} {neg _}    div-a = div-negate div-a

div-abs-left : {d a : ℤ} -> d div a -> (abs d) div a
div-abs-left {zero-int} div-a = div-a
div-abs-left {pos _}    div-a = div-a
div-abs-left {neg _}    div-a = div-negate-left div-a


private
  Unit : (x : Int) -> Type₀
  Unit zero-int = Bot
  Unit (pos zero) = Top
  Unit (pos (suc _)) = Bot
  Unit (neg zero) = Top
  Unit (neg (suc _)) = Bot

  abs-one-implies-unit : {m : Int} -> abs' m == 1 -> Unit m
  abs-one-implies-unit {zero-int} pr = zero-suc-absurd pr
  abs-one-implies-unit {pos zero} _ = tt
  abs-one-implies-unit {pos (suc _)} pr = zero-suc-absurd (suc-injective (sym pr))
  abs-one-implies-unit {neg zero} _ = tt
  abs-one-implies-unit {neg (suc _)} pr = zero-suc-absurd (suc-injective (sym pr))


  *'-one-implies-one : {m n : Nat} -> m *' n == 1 -> n == 1
  *'-one-implies-one {zero} {_} pr = zero-suc-absurd pr
  *'-one-implies-one {suc m} {zero} pr = *'-one-implies-one {m} {zero} pr
  *'-one-implies-one {suc zero} {suc zero} _ = refl
  *'-one-implies-one {suc zero} {suc (suc n)} pr = zero-suc-absurd (sym (suc-injective pr))
  *'-one-implies-one {suc (suc m)} {suc (suc n)} pr = zero-suc-absurd (sym (suc-injective pr))
  *'-one-implies-one {suc (suc m)} {suc zero} pr = zero-suc-absurd (sym (suc-injective pr))

  *-one-implies-unit : {m n : Int} -> m * n == (int 1) -> Unit n
  *-one-implies-unit {m} {n} pr = (abs-one-implies-unit abs-pr)
    where
    pr1 : abs' m *' abs' n == 1
    pr1 = (sym (abs'-inject-* {m} {n})) >=> (cong abs' pr)
    abs-pr : (abs' n) == 1
    abs-pr = *'-one-implies-one {abs' m} {abs' n} pr1

  nonneg-unit->one : {n : Int} -> NonNeg n -> Unit n -> n == (int 1)
  nonneg-unit->one {n = nonneg (suc zero)} _ _ = refl
  nonneg-unit->one {n = neg _} (inj-l ())
  nonneg-unit->one {n = neg _} (inj-r ())



divℤ-one->one : {d : Int} -> NonNeg d -> d div (int 1) -> d == (int 1)
divℤ-one->one nn d%1 =
  unsquash (isSetInt _ _) (∥-map (\ (m , p) -> nonneg-unit->one nn (*-one-implies-unit p)) d%1)
