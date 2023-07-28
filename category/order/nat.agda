{-# OPTIONS --cubical --safe --exact-split #-}

module category.order.nat where

open import base
open import category.base
open import category.order
open import nat
open import order.instances.nat

ℕ≤C : PreCategory ℓ-zero ℓ-zero
ℕ≤C = PartialOrderC ℕ

instance
  isThin-ℕ≤C : isThin ℕ≤C
  isThin-ℕ≤C = isThin-PartialOrderC ℕ

  isUnivalent-ℕ≤C : isUnivalent ℕ≤C
  isUnivalent-ℕ≤C = isUnivalent-PartialOrderC ℕ isSetNat
