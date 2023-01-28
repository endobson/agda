{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax.instances.nat where

open import base
open import order.instances.nat
open import order.minmax
open import order.minmax.decidable

instance
  MinOperationStr-ℕ : MinOperationStr useⁱ
  MinOperationStr-ℕ = MinOperationStr-Decidable Nat
  MaxOperationStr-ℕ : MaxOperationStr useⁱ
  MaxOperationStr-ℕ = MaxOperationStr-Decidable Nat
