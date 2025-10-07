{-# OPTIONS --cubical --safe --exact-split #-}

module int.order where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int
open import order
open import order.instances.int
open import order.instances.nat

-- Basic facts for constants
opaque
  0≤nonneg : (n : Nat) -> 0# ≤ int n
  0≤nonneg n = (n , +-right-zero)

  0<pos : (n : Nat) -> 0# < pos n
  0<pos n = (suc n , tt) , +-right-zero

  neg<0 : (n : Nat) -> neg n < 0#
  neg<0 n = (suc n , tt) , +-inverse


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

-- Order <-> Sign lemmas

opaque
  0<->Pos : {i : Int} -> 0# < i -> Pos i
  0<->Pos ((_ , pos-x) , path) = subst Pos path (+-Pos-NonNeg (Pos'->Pos pos-x) (NonNeg-nonneg 0))

  Pos->0< : {i : Int} -> Pos i -> 0# < i
  Pos->0< {pos i} _ = 0<pos i
  Neg-><0 : {i : Int} -> Neg i -> i < 0#
  Neg-><0 {neg i} _ = neg<0 i


  0≤->NonNeg : {i : Int} -> (int 0) ≤ i -> NonNeg i
  0≤->NonNeg (x , path) = subst NonNeg path (+-NonNeg-NonNeg (NonNeg-nonneg x) (NonNeg-nonneg 0))
  NonNeg->0≤ : {i : Int} -> NonNeg i -> (int 0) ≤ i
  NonNeg->0≤ {nonneg i} _ = i , +-right-zero
  NonNeg->0≤ {neg i} (inj-l ())
  NonNeg->0≤ {neg i} (inj-r ())
