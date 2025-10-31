{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax.instances.int where

open import base
open import int.base
open import order.instances.int
open import order.minmax
open import order.minmax.decidable

instance
  opaque
    MinOperationStr-ℤ : MinOperationStr useⁱ
    MinOperationStr-ℤ = MinOperationStr-Decidable ℤ
    MaxOperationStr-ℤ : MaxOperationStr useⁱ
    MaxOperationStr-ℤ = MaxOperationStr-Decidable ℤ
