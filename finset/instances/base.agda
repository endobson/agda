{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances.base where

open import base
open import equality-path
open import equivalence
open import fin
open import fin-algebra
open import finset
open import truncation
open import type-algebra

private
  variable
    ℓ : Level

abstract
  isFinSet-Bot : isFinSet Bot
  isFinSet-Bot = ∣ 0 , equiv⁻¹ Fin-Bot-eq ∣

FinSet-Bot : FinSet ℓ-zero
FinSet-Bot = Bot , isFinSet-Bot

instance
  FinSetStr-Bot : FinSetStr Bot
  FinSetStr-Bot = record { isFin = isFinSet-Bot }

abstract
  isFinSet-Top : isFinSet Top
  isFinSet-Top = ∣ 1 , equiv⁻¹ Fin-Top-eq ∣

FinSet-Top : FinSet ℓ-zero
FinSet-Top = Top , isFinSet-Top

instance
  FinSetStr-Top : FinSetStr Top
  FinSetStr-Top = record { isFin = isFinSet-Top }

abstract
  isFinSet-Uninhabited : {A : Type ℓ} -> ¬ A -> isFinSet A
  isFinSet-Uninhabited ¬A = ∣ 0 , (¬-Bot-eq ¬A) >eq> (equiv⁻¹ Fin-Bot-eq) ∣

abstract
  isFinSet-Lift : {A : Type ℓ} (ℓ₂ : Level) -> isFinSet A -> isFinSet (Lift ℓ₂ A)
  isFinSet-Lift {A = A} ℓ₂  = ∥-map handle
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Σ[ n ∈ Nat ] (Lift ℓ₂ A ≃ Fin n)
    handle (n , eq) = n , liftEquiv ℓ₂ A >eq> eq

FinSet-Lift : {ℓ : Level} (ℓ₂ : Level) -> FinSet ℓ -> FinSet (ℓ-max ℓ ℓ₂)
FinSet-Lift ℓ₂ (A , fsA) = Lift ℓ₂ A , isFinSet-Lift ℓ₂ fsA