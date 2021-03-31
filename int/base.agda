{-# OPTIONS --cubical --safe --exact-split #-}

module int.base where

open import base

data Int : Set where
 -- nonneg n Corresponds to n
 nonneg : Nat -> Int
 -- neg n Corresponds to -(n+1)
 neg : Nat -> Int

ℤ = Int

pattern zero-int = nonneg zero
pattern pos x = nonneg (suc x)

int : Nat -> Int
int = nonneg

ℕ->ℤ : Nat -> Int
ℕ->ℤ = nonneg
