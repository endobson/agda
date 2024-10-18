{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax.instances.nat where

open import base
open import nat.order.base
open import order.instances.nat
open import order.minmax
open import order.minmax.decidable

instance
  opaque
    MinOperationStr-ℕ : MinOperationStr useⁱ
    MinOperationStr-ℕ = MinOperationStr-Decidable Nat
    MaxOperationStr-ℕ : MaxOperationStr useⁱ
    MaxOperationStr-ℕ = MaxOperationStr-Decidable Nat
  GlobalMinOperationStr-ℕ : GlobalMinOperationStr useⁱ
  GlobalMinOperationStr-ℕ = record
    { global-min = 0
    ; global-min-≮ = zero-≮
    }
