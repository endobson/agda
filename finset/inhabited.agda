{-# OPTIONS --cubical --safe --exact-split #-}

module finset.inhabited where

open import base
open import equivalence
open import fin
open import finset
open import hlevel.base
open import truncation

private
  variable
    ℓ : Level
    A : Type ℓ

isFin⁺Set : Type ℓ -> Type ℓ
isFin⁺Set A = isFinSet A × ∥ A ∥

Fin⁺Set : (ℓ : Level) -> Type (ℓ-suc ℓ)
Fin⁺Set ℓ = Σ[ t ∈ Type ℓ ] (isFin⁺Set t)

record Fin⁺SetStr (A : Type ℓ) : Type ℓ where
  field
    isFin : isFinSet A
    inhabited : ∥ A ∥

-- Equivalence for Fin⁺Sets

Fin⁺Set-eq : (A : Fin⁺Set ℓ) -> Σ[ n ∈ Nat ] ∥ ⟨ A ⟩ ≃ Fin (suc n) ∥
Fin⁺Set-eq (A , ∣n,eq∣ , ∣a∣) = handle (isFinSet->isFinSetΣ ∣n,eq∣)
  where
  handle : Σ[ n ∈ Nat ] ∥ A ≃ Fin n ∥ -> Σ[ n ∈ Nat ] ∥ A ≃ Fin (suc n) ∥
  handle (zero , eq) =
    bot-elim (unsquash isPropBot (∥-map2 (\eq a -> ¬fin-zero (eqFun eq a)) eq ∣a∣))
  handle (suc n , eq) = (n , eq)
