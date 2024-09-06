{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances.sum where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finset
open import finset.inhabited
open import nat
open import sum
open import truncation

isFinSetΣ-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} -> isFinSetΣ A -> isFinSetΣ B
              -> isFinSetΣ (A ⊎ B)
isFinSetΣ-⊎ {A = A} {B} (na , eq-a) (nb , eq-b) = (na +' nb , ∥-map2 handle eq-a eq-b)
  where
  opaque
    handle : (A ≃ Fin na) -> (B ≃ Fin nb) -> (A ⊎ B) ≃ Fin (na +' nb)
    handle eq-a eq-b = ∘-equiv (pathToEquiv (\i -> (sym (Fin-+ na nb)) i)) (⊎-equiv eq-a eq-b)

isFinSet-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} -> isFinSet A -> isFinSet B
             -> isFinSet (A ⊎ B)
isFinSet-⊎ FA FB = isFinSetΣ->isFinSet (isFinSetΣ-⊎ (isFinSet->isFinSetΣ FA) (isFinSet->isFinSetΣ FB))

FinSet-⊎ : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) -> (B : FinSet ℓ₂) -> FinSet (ℓ-max ℓ₁ ℓ₂)
FinSet-⊎ (A , finA) (B , finB) = (A ⊎ B) , isFinSet-⊎ finA finB

Fin⁺Set-⊎ : {ℓ₁ ℓ₂ : Level} -> (A : Fin⁺Set ℓ₁) -> (B : Fin⁺Set ℓ₂) -> Fin⁺Set (ℓ-max ℓ₁ ℓ₂)
Fin⁺Set-⊎ (A , finA , ∣a∣) (B , finB , ∣b∣) =
  (A ⊎ B) , isFinSet-⊎ finA finB , ∥-map inj-l ∣a∣

instance
  FinSetStr-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {{FA : FinSetStr A}}
                {{FB : FinSetStr B}} -> FinSetStr (A ⊎ B)
  FinSetStr-⊎ {{FA = FA}} {{FB = FB}} = record
    { isFin = isFinSet-⊎ (FinSetStr.isFin FA) (FinSetStr.isFin FB)
    }

  Fin⁺SetStr-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {{FA : Fin⁺SetStr A}}
                 {{FB : Fin⁺SetStr B}} -> Fin⁺SetStr (A ⊎ B)
  Fin⁺SetStr-⊎ {{FA = FA}} {{FB = FB}} = record
    { isFin = isFinSet-⊎ (Fin⁺SetStr.isFin FA) (Fin⁺SetStr.isFin FB)
    ; inhabited = ∥-map inj-l (Fin⁺SetStr.inhabited FA)
    }
