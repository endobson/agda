{-# OPTIONS --cubical --safe --exact-split #-}

module subfinite where

open import base
open import cubical
open import equivalence
open import fin
open import finset
open import finset.instances
open import functions
open import functions.injective
open import isomorphism
open import truncation

private
  variable
    ℓ : Level
    A : Type ℓ

isBFinSetΣ : Type ℓ -> (ℓ₂ : Level) -> Type (ℓ-max ℓ (ℓ-suc ℓ₂))
isBFinSetΣ A ℓ₂ = Σ[ B ∈ (FinSet ℓ₂) ] (Σ (A -> ⟨ B ⟩) Injective)

isBFinSetΣ⁻ : Type ℓ -> Type ℓ
isBFinSetΣ⁻ A = Σ[ n ∈ Nat ] (Σ (A -> Fin n) Injective)

isBFinSet : Type ℓ -> (ℓ₂ : Level) -> Type (ℓ-max ℓ (ℓ-suc ℓ₂))
isBFinSet A ℓ = ∥ isBFinSetΣ A ℓ ∥

isBFinSet⁻ : Type ℓ -> Type ℓ
isBFinSet⁻ A = ∥ isBFinSetΣ⁻ A ∥

BFinSet : (ℓ₁ ℓ₂ : Level) -> Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
BFinSet ℓ₁ ℓ₂ = Σ[ A ∈ (Type ℓ₁) ] (isBFinSet A ℓ₂)

BFinSet⁻ : (ℓ₁ : Level) -> Type (ℓ-suc ℓ₁)
BFinSet⁻ ℓ₁  = Σ[ A ∈ (Type ℓ₁) ] (isBFinSet⁻ A)

-- 

isBFinSet⁻-eq : {ℓ₂ : Level} {A : Type ℓ} -> isBFinSet⁻ A ≃ isBFinSet A ℓ₂
isBFinSet⁻-eq {A = A} = isoToEquiv (isProp->iso g f squash squash)
  where
  f : isBFinSet A _ -> isBFinSet⁻ A
  f bfs = ∥-bind handle bfs
    where
    handle : isBFinSetΣ A _ -> isBFinSet⁻ A
    handle ((B , fsB) , (f , inj-f)) = ∥-map handle2 fsB
      where
      handle2 : Σ[ n ∈ Nat ] (B ≃ Fin n) -> isBFinSetΣ⁻ A
      handle2 (n , eqB) = n , (eqFun eqB ∘ f) , 
                          (∘-Injective (Retraction->Injective (eqInv eqB , eqRet eqB)) inj-f)

  g : isBFinSet⁻ A -> isBFinSet A _
  g bfs = ∥-map handle bfs
    where
    handle : isBFinSetΣ⁻ A -> isBFinSetΣ A _
    handle (n , f , inj-f) = 
      FinSet-Lift _ (FinSet-Fin n) , lift ∘ f ,
      (∘-Injective (Retraction->Injective (Lift.lower , \_ -> refl)) inj-f)

