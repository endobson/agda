{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances.boolean where

open import finset
open import base
open import type-algebra.boolean
open import truncation
open import equivalence

isFinSet-Boolean : isFinSet Boolean
isFinSet-Boolean = ∣ 2 , equiv⁻¹ Fin2≃Boolean ∣

FinSet-Boolean : FinSet ℓ-zero
FinSet-Boolean = Boolean , isFinSet-Boolean

instance
  FinSetStr-Boolean : FinSetStr Boolean
  FinSetStr-Boolean = record { isFin = isFinSet-Boolean }
