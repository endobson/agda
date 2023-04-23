{-# OPTIONS --cubical --safe --exact-split #-}

module countable-set where

open import base
open import relation
open import equivalence
open import truncation

isCountableSet' : {ℓ : Level} -> Pred (Type ℓ) ℓ
isCountableSet' T = T ≃ Nat

isCountableSet : {ℓ : Level} -> Pred (Type ℓ) ℓ
isCountableSet T = ∥ isCountableSet' T ∥

CountableSet : (ℓ : Level) -> Type (ℓ-suc ℓ)
CountableSet ℓ = Σ (Type ℓ) isCountableSet
