{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax.instances.rational where

open import base
open import rational
open import order.instances.rational
open import order.minmax
open import order.minmax.decidable

instance
  MinOperationStr-ℚ : MinOperationStr useⁱ
  MinOperationStr-ℚ = MinOperationStr-Decidable ℚ
  MaxOperationStr-ℚ : MaxOperationStr useⁱ
  MaxOperationStr-ℚ = MaxOperationStr-Decidable ℚ
