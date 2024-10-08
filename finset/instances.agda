{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import finset
open import finset.inhabited
open import fin-algebra
open import isomorphism
open import maybe
open import truncation
open import type-algebra

private
  variable
    ℓ : Level

isFinSet-Fin : {n : Nat} -> isFinSet (Fin n)
isFinSet-Fin {n = n} = ∣ n , pathToEquiv (\i -> Fin n) ∣

FinSet-Fin : (n : Nat) -> FinSet ℓ-zero
FinSet-Fin n = Fin n , isFinSet-Fin

instance
  FinSetStr-Fin : {n : Nat} -> FinSetStr (Fin n)
  FinSetStr-Fin = record { isFin = isFinSet-Fin }

isFinSet-FinT : {n : Nat} -> isFinSet (FinT n)
isFinSet-FinT {n = n} = ∣ n , pathToEquiv (\i -> FinT=Fin n i) ∣

FinSet-FinT : (n : Nat) -> FinSet ℓ-zero
FinSet-FinT n = FinT n , isFinSet-FinT


instance
  Fin⁺SetStr-Fin : {n : Nat} -> Fin⁺SetStr (Fin (suc n))
  Fin⁺SetStr-Fin = record
    { isFin = isFinSet-Fin
    ; inhabited = ∣ zero-fin ∣
    }


abstract
  isFinSet-Maybe : {ℓ : Level} {A : Type ℓ} -> isFinSet A -> isFinSet (Maybe A)
  isFinSet-Maybe {A = A} = ∥-map handle
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Σ[ n ∈ Nat ] (Maybe A ≃ Fin n)
    handle (n , eq) = suc n , (Maybe-eq eq) >eq> (equiv⁻¹ (Fin-Maybe-eq n))

FinSet-Maybe : {ℓ : Level} -> FinSet ℓ -> FinSet ℓ
FinSet-Maybe (A , finA) = Maybe A , isFinSet-Maybe finA


instance
  FinSetStr-Maybe : {ℓ : Level} {A : Type ℓ} {{FA : FinSetStr A}} -> FinSetStr (Maybe A)
  FinSetStr-Maybe {{FA = FA}} = record { isFin = isFinSet-Maybe (FinSetStr.isFin FA) }

  Fin⁺SetStr-Maybe : {ℓ : Level} {A : Type ℓ} {{FA : Fin⁺SetStr A}} -> Fin⁺SetStr (Maybe A)
  Fin⁺SetStr-Maybe {{FA = FA}} = record
    { isFin = isFinSet-Maybe (Fin⁺SetStr.isFin FA)
    ; inhabited = ∣ nothing ∣
    }

abstract
  isFinSet-isContr : {A : Type ℓ} -> isContr A -> isFinSet A
  isFinSet-isContr isContr-A = ∣ 1 , (∘-equiv (equiv⁻¹ Fin-Top-eq) (Contr-Top-eq isContr-A)) ∣
