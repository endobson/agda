{-# OPTIONS --cubical --safe --exact-split #-}

module finset.inhabited where

open import base
open import equivalence
open import fin
open import finset
open import hlevel.base
open import hlevel.sigma
open import hlevel.sum
open import truncation

private
  variable
    ℓ : Level
    A : Type ℓ

isFin⁺Set : Type ℓ -> Type ℓ
isFin⁺Set A = isFinSet A × ∥ A ∥

isProp-isFin⁺Set : isProp (isFin⁺Set A)
isProp-isFin⁺Set = isProp× isProp-isFinSet squash

Fin⁺Set : (ℓ : Level) -> Type (ℓ-suc ℓ)
Fin⁺Set ℓ = Σ[ t ∈ Type ℓ ] (isFin⁺Set t)

record Fin⁺SetStr (A : Type ℓ) : Type ℓ where
  field
    isFin : isFinSet A
    inhabited : ∥ A ∥

get-Fin⁺Setⁱ : {ℓ : Level} (I : Type ℓ) {{FI : Fin⁺SetStr I}} -> Fin⁺Set ℓ
get-Fin⁺Setⁱ I {{FI = FI}} = I , Fin⁺SetStr.isFin FI , Fin⁺SetStr.inhabited FI


-- Equivalence for Fin⁺Sets

Fin⁺Set-eq : (A : Fin⁺Set ℓ) -> Σ[ n ∈ Nat ] ∥ ⟨ A ⟩ ≃ Fin (suc n) ∥
Fin⁺Set-eq (A , ∣n,eq∣ , ∣a∣) = handle (isFinSet->isFinSetΣ ∣n,eq∣)
  where
  handle : Σ[ n ∈ Nat ] ∥ A ≃ Fin n ∥ -> Σ[ n ∈ Nat ] ∥ A ≃ Fin (suc n) ∥
  handle (zero , eq) =
    bot-elim (unsquash isPropBot (∥-map2 (\eq a -> ¬fin-zero (eqFun eq a)) eq ∣a∣))
  handle (suc n , eq) = (n , eq)

opaque
  decide-isFin⁺Set : isFinSet A -> (isFin⁺Set A) ⊎ (¬ A)
  decide-isFin⁺Set {A = A} fs = unsquash isProp-Ans (∥-map handle fs)
    where
    Ans : Type (levelOf A)
    Ans = isFin⁺Set A ⊎ ¬ A
    isProp-Ans : isProp Ans
    isProp-Ans =
      isProp⊎ isProp-isFin⁺Set isProp¬
        (\ (_ , ∣a∣) ¬a -> unsquash isPropBot (∥-map ¬a ∣a∣))

    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Ans
    handle (zero  , eq) = inj-r (\a -> ¬fin-zero (eqFun eq a))
    handle (suc n , eq) = inj-l (fs , ∣ eqInv eq zero-fin ∣)
