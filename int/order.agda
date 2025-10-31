{-# OPTIONS --cubical --safe --exact-split #-}

module int.order where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int.add1
open import int.addition
open import int.base
open import int.cover
open import int.nat
open import nat
open import order
open import order.instances.int
open import order.instances.nat

-- Basic facts for constants
opaque
  0≤nonneg : {n : Nat} -> 0# ≤ int n
  0≤nonneg {n} = (n , +-right-zero)

  0<pos : {n : Nat} -> 0# < pos n
  0<pos {n} = (suc n , tt) , +-right-zero

  neg<0 : {n : Nat} -> neg n < 0#
  neg<0 {n} = (suc n , tt) , +-inverse


-- Basic facts for add1/sub1
opaque
  add1-weaken-< : {a b : Int} -> a < b -> add1 a ≤ b
  add1-weaken-< ((suc i , tt) , p) = i , add1-extract-right >=> sym add1-extract-left >=> p

  sub1-weaken-< : {a b : Int} -> a < b -> a ≤ sub1 b
  sub1-weaken-< ((suc i , tt) , p) = i , sub1-extract-left >=> cong sub1 p

  add1-< : {n : Int} -> n < (add1 n)
  add1-< = 1⁺ , ℤ+-eval

  sub1-< : {n : Int} -> (sub1 n) < n
  sub1-< = 1⁺ , sub1-extract-right >=> cong sub1 ℤ+-eval >=> sub1-add1-id

-- ℕ->ℤ preserves order
opaque
  ℕ->ℤ-preserves-< : {a b : Nat} -> a < b -> int a < int b
  ℕ->ℤ-preserves-< {a} {b} (d , d+sa=b) = (suc d , tt) ,
    add1-extract-left >=>
    sym add1-extract-right >=>
    sym ℕ->ℤ-+ >=>
    cong int (d+sa=b)

  ℕ->ℤ-preserves-≤ : {a b : Nat} -> a ≤ b -> int a ≤ int b
  ℕ->ℤ-preserves-≤ {a} {b} (d , d+a=b) = d ,
    sym ℕ->ℤ-+ >=>
    cong int (d+a=b)

  ℕ->ℤ-reflects-< : {a b : Nat} -> (int a) < (int b) -> a < b
  ℕ->ℤ-reflects-< {a} {b} ((suc i , _) , p) =
    i , nonneg-injective (
      ℕ->ℤ-+ >=>
      add1-extract-right >=> sym add1-extract-left >=> p)

  ℕ->ℤ-reflects-≤ : {a b : Nat} -> (int a) ≤ (int b) -> a ≤ b
  ℕ->ℤ-reflects-≤ {a} {b} (i , p) =
    i , nonneg-injective (ℕ->ℤ-+ >=> p)
