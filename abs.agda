{-# OPTIONS --cubical --safe --exact-split #-}

module abs where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality-path
open import int
open import int.add1
open import int.base
open import int.cover
open import int.nat
open import int.order
open import int.sign
open import nat
open import order
open import order.instances.int
open import order.minmax.instances.int
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.int
open import ordered-semiring
open import ordered-semiring.instances.int
open import ring
open import ring.implementations.int
open import semiring
open import semiring.instances.nat
open import sum

abs' : Int -> Nat
abs' (nonneg x) = x
abs' (neg x) = suc x

opaque
  abs'-abs-path : ∀ {i : Int} -> int (abs' i) == abs i
  abs'-abs-path {nonneg x} =
    sym (abs-0≤-path 0≤nonneg)
  abs'-abs-path {neg x} =
    sym (abs-≤0-path (weaken-< neg<0))

  nonneg-abs' : {m : Int} -> (NonNeg m) -> m == int (abs' m)
  nonneg-abs' {nonneg m} _ = refl
  nonneg-abs' {neg m} 0≤m = bot-elim (convert-≤ 0≤m neg<0)

  nonpos-abs' : {m : Int} -> (NonPos m) -> m == - int (abs' m)
  nonpos-abs' {pos m}    m≤0 = bot-elim (convert-≤ m≤0 0<pos)
  nonpos-abs' {zero-int} _   = refl
  nonpos-abs' {neg _}    _   = refl

  Pos'-abs' : {m : Int} -> NonZero m -> Pos' (abs' m)
  Pos'-abs' {zero-int} nz = bot-elim (NonZero->!=0 nz refl)
  Pos'-abs' {pos n}    _  = tt
  Pos'-abs' {neg n}    _  = tt

  abs'-inject-add1 : {m : Int} -> (NonNeg m) -> abs' (add1 m) == suc (abs' m)
  abs'-inject-add1 0≤m =
    nonneg-injective (
      sym (nonneg-abs' (weaken-< (trans-≤-< 0≤m add1-<))) >=>
      cong add1 (nonneg-abs' 0≤m))

  abs'-inject-+ : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> abs' (m + n) == abs' m +' abs' n
  abs'-inject-+ {m} {n} 0≤m 0≤n =
    nonneg-injective (
      sym (nonneg-abs' (+-preserves-0≤ 0≤m 0≤n)) >=>
      (+-cong (nonneg-abs' 0≤m) (nonneg-abs' 0≤n)) >=>
      sym ℕ->ℤ-+)

  abs'-inject-*/non-neg : {m n : Int} -> NonNeg m -> NonNeg n -> abs' (m * n) == abs' m *' abs' n
  abs'-inject-*/non-neg {m} {n} 0≤m 0≤n =
    nonneg-injective (
      sym (nonneg-abs' (*-preserves-0≤ 0≤m 0≤n)) >=>
      (*-cong (nonneg-abs' 0≤m) (nonneg-abs' 0≤n)) >=>
      sym ℕ->ℤ-*)

  abs'-cancel-minus : {m : Int} -> abs' (- m) == abs' m
  abs'-cancel-minus {zero-int} = refl
  abs'-cancel-minus {pos _} = refl
  abs'-cancel-minus {neg _} = refl


  abs'-inject-* : {m n : Int} -> abs' (m * n) == abs' m *' abs' n
  abs'-inject-* {m} {n} = handle (split-≤ m) (split-≤ n)
    where
    split-≤ : (m : Int) -> (m ≤ 0#) ⊎ (0# ≤ m)
    split-≤ m = ⊎-map weaken-< (\x -> x) (split-< m 0#)

    handle : (m ≤ 0# ⊎ 0# ≤ m) -> (n ≤ 0# ⊎ 0# ≤ n) -> abs' (m * n) == abs' m *' abs' n
    handle (inj-l m≤0) (inj-l n≤0) =
      cong abs' (sym minus-extract-both) >=>
      abs'-inject-*/non-neg (minus-flips-≤0 m≤0) (minus-flips-≤0 n≤0) >=>
      *-cong (abs'-cancel-minus {m}) (abs'-cancel-minus {n})
    handle (inj-l m≤0) (inj-r 0≤n) =
      sym (abs'-cancel-minus {m * n}) >=>
      cong abs' (sym minus-extract-left) >=>
      abs'-inject-*/non-neg (minus-flips-≤0 m≤0) 0≤n >=>
      *-left (abs'-cancel-minus {m})
    handle (inj-r 0≤m) (inj-l n≤0) =
      sym (abs'-cancel-minus {m * n}) >=>
      cong abs' (sym minus-extract-right) >=>
      abs'-inject-*/non-neg 0≤m (minus-flips-≤0 n≤0) >=>
      cong (abs' m *_) (abs'-cancel-minus {n})
    handle (inj-r 0≤m) (inj-r 0≤n) =
      abs'-inject-*/non-neg 0≤m 0≤n
