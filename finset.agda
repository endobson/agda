{-# OPTIONS --cubical --safe --exact-split #-}

module finset where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import fin-algebra
open import functions
open import hlevel
open import isomorphism
open import nat
open import sigma
open import truncation

private
  variable
    ℓ : Level
    A : Type ℓ

isFinSet : Type ℓ -> Type ℓ
isFinSet A = ∃[ n ∈ Nat ] (A ≃ Fin n)

isFinSetFin : {n : Nat} -> isFinSet (Fin n)
isFinSetFin {n = n} = ∣ _ , pathToEquiv (\i -> Fin n) ∣

isFinSetTop : isFinSet Top
isFinSetTop = ∣ _ , pathToEquiv (\i -> Fin-Top (~ i)) ∣

isFinSetΣ : Type ℓ -> Type ℓ
isFinSetΣ A = Σ[ n ∈ Nat ] ∥ (A ≃ Fin n) ∥

isFinSetΣ->isFinSet : isFinSetΣ A -> isFinSet A
isFinSetΣ->isFinSet {A = A} (n , ∥eq∥) = ∥-map (\ eq -> (n , eq)) ∥eq∥

isProp-isFinSetΣ : {A : Type₀} -> isProp (isFinSetΣ A)
isProp-isFinSetΣ {A = A} (n , n-equiv) (m , m-equiv) = ΣProp-path squash n==m
  where

  work : (A ≃ Fin n) -> (A ≃ Fin m) -> n == m
  work neq meq = Fin-injective (sym (ua neq) >=> ua meq)

  n==m : n == m
  n==m = unsquash (isSetNat n m)
           (unsquash squash
             (∥-map (\neq -> ∥-map (\meq -> work neq meq) m-equiv) n-equiv))

isFinSet->isFinSetΣ : {A : Type₀} -> isFinSet A -> isFinSetΣ A
isFinSet->isFinSetΣ ∣ n , eq ∣ = n , ∣ eq ∣
isFinSet->isFinSetΣ (squash x y i) =
  isProp-isFinSetΣ (isFinSet->isFinSetΣ x) (isFinSet->isFinSetΣ y) i

isFinSet==isFinSetΣ : {A : Type₀} -> isFinSet A == isFinSetΣ A
isFinSet==isFinSetΣ {A = A} =
  ua (isoToEquiv (iso isFinSet->isFinSetΣ isFinSetΣ->isFinSet
                      (\ _ -> isProp-isFinSetΣ _ _)
                      (\ _ -> squash _ _)))

FinSet : (ℓ : Level) -> Type (ℓ-suc ℓ)
FinSet ℓ = Σ[ t ∈ Type ℓ ] isFinSet t

cardnality : FinSet ℓ-zero -> Nat
cardnality (_ , p) = fst (transport isFinSet==isFinSetΣ p)

extract : {n : Nat} -> ∥ (A ≃ Fin n) ∥ ->
          (f : (A ≃ Fin n) -> Nat) ->
          2-Constant f -> Nat
extract equiv f f-const = ∥->Set isSetNat f f-const equiv
