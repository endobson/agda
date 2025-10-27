{-# OPTIONS --cubical --safe --exact-split #-}

module int.nat where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int.add1
open import int.addition
open import int.base
open import int.multiplication
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ring.implementations.int
open import semiring

-- Nat arithmetic -> Integer arithmetic

ℕ->ℤ-minus : {m n : Nat} -> m < n -> ℕ->ℤ (n -' m) == (ℕ->ℤ n) + (- (ℕ->ℤ m))
ℕ->ℤ-minus {zero}  lt = sym +-right-zero
ℕ->ℤ-minus {suc _} {zero} lt = bot-elim (zero-≮ lt)
ℕ->ℤ-minus {suc m} {suc n} lt =
  ℕ->ℤ-minus (pred-≤ lt) >=>
  sub1-extract-left >=>
  sym sub1-extract-right >=>
  +-right sub1-minus->minus-add1

ℕ->ℤ-+ : {m n : Nat} -> int (m +' n) == int m + int n
ℕ->ℤ-+ {zero} = sym +-left-zero
ℕ->ℤ-+ {suc m} = cong add1 ℕ->ℤ-+ >=> sym add1-extract-left

ℕ->ℤ-* : {m n : Nat} -> int (m *' n) == int m * int n
ℕ->ℤ-* {zero} = sym *-left-zero
ℕ->ℤ-* {suc m} = ℕ->ℤ-+ >=> +-right ℕ->ℤ-* >=> sym add1-extract-*
