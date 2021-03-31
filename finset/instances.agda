{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import finset
open import fin-algebra
open import isomorphism
open import maybe
open import truncation
open import type-algebra


private
  abstract
    isFinSet-Bot : isFinSet Bot
    isFinSet-Bot = ∣ 0 , pathToEquiv (\i -> Fin-Bot (~ i)) ∣

FinSet-Bot : FinSet ℓ-zero
FinSet-Bot = Bot , isFinSet-Bot

private
  abstract
    isFinSet-Top : isFinSet Top
    isFinSet-Top = ∣ 1 , pathToEquiv (\i -> Fin-Top (~ i)) ∣

FinSet-Top : FinSet ℓ-zero
FinSet-Top = Top , isFinSet-Top

private
  abstract
    isFinSet-Fin : {n : Nat} -> isFinSet (Fin n)
    isFinSet-Fin {n = n} = ∣ n , pathToEquiv (\i -> Fin n) ∣

FinSet-Fin : (n : Nat) -> FinSet ℓ-zero
FinSet-Fin n = Fin n , isFinSet-Fin

private
  abstract
    isFinSet-Maybe : {ℓ : Level} {A : Type ℓ} -> isFinSet A -> isFinSet (Maybe A)
    isFinSet-Maybe {A = A} = ∥-map handle
      where
      handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Σ[ n ∈ Nat ] (Maybe A ≃ Fin n)
      handle (n , eq) = suc n , (Maybe-eq eq) >eq> (equiv⁻¹ (Fin-Maybe-eq n))

FinSet-Maybe : {ℓ : Level} -> FinSet ℓ -> FinSet ℓ
FinSet-Maybe (A , finA) = Maybe A , isFinSet-Maybe finA
