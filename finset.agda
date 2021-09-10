{-# OPTIONS --cubical --safe --exact-split #-}

module finset where

open import base
open import cubical
open import equality
open import equivalence
open import univalence
open import fin
open import fin-algebra
open import functions
open import hlevel
open import isomorphism
open import nat
open import relation
open import sigma
open import truncation
open import univalence

private
  variable
    ℓ : Level
    A B : Type ℓ

isFinSet : Type ℓ -> Type ℓ
isFinSet A = ∃[ n ∈ Nat ] (A ≃ Fin n)

isFinSetΣ : Type ℓ -> Type ℓ
isFinSetΣ A = Σ[ n ∈ Nat ] ∥ (A ≃ Fin n) ∥

isProp-isFinSet : {ℓ : Level} {A : Type ℓ} -> isProp (isFinSet A)
isProp-isFinSet = squash

isProp-isFinSetΣ : {ℓ : Level} {A : Type ℓ} -> isProp (isFinSetΣ A)
isProp-isFinSetΣ {ℓ} {A = A} (n , n-equiv) (m , m-equiv) = ΣProp-path squash n==m
  where
  work : (A ≃ (Fin n)) -> (A ≃ (Fin m)) -> n == m
  work eqn eqm = Fin-injective (isoToPath ((equivToIso eqm) ∘ⁱ iso⁻¹ (equivToIso eqn)))

  n==m : n == m
  n==m = unsquash (isSetNat n m)
           (unsquash squash
             (∥-map (\neq -> ∥-map (\meq -> work neq meq) m-equiv) n-equiv))

isFinSet->isSet : isFinSet A -> isSet A
isFinSet->isSet {A = A} fs = unsquash isProp-isSet (∥-map handle fs)
  where
  handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> isSet A
  handle (_ , eq) = ≃-isSet (equiv⁻¹ eq) isSetFin

isFinSet->Discrete : isFinSet A -> Discrete A
isFinSet->Discrete fs = unsquash (isPropΠ2 (\_ _ -> isPropDec (isFinSet->isSet fs _ _))) (∥-map handle fs)
  where
  handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Discrete A
  handle (n , eq) a1 a2 = handle2 (decide-fin (f a1) (f a2))
    where
    f = eqFun eq
    g = eqInv eq
    ret = eqRet eq
    handle2 : Dec (f a1 == f a2) -> Dec (a1 == a2)
    handle2 (yes p) = yes (sym (ret a1) >=> cong g p >=> ret a2)
    handle2 (no ¬p) = no (\p -> ¬p (cong f p))

-- The two notions of finite sets are the same.

isFinSetΣ->isFinSet : isFinSetΣ A -> isFinSet A
isFinSetΣ->isFinSet {A = A} (n , ∥eq∥) = ∥-map (\ eq -> (n , eq)) ∥eq∥

isFinSet->isFinSetΣ : {ℓ : Level} {A : Type ℓ} -> isFinSet A -> isFinSetΣ A
isFinSet->isFinSetΣ ∣ n , eq ∣ = n , ∣ eq ∣
isFinSet->isFinSetΣ (squash x y i) =
  isProp-isFinSetΣ (isFinSet->isFinSetΣ x) (isFinSet->isFinSetΣ y) i

isFinSet≃isFinSetΣ : isFinSet A ≃ isFinSetΣ A
isFinSet≃isFinSetΣ =
  (isoToEquiv (iso isFinSet->isFinSetΣ isFinSetΣ->isFinSet
                   (\ _ -> isProp-isFinSetΣ _ _)
                   (\ _ -> squash _ _)))

-- Equivalence allows conversion, even across universe levels.

isFinSet-equiv : A ≃ B -> isFinSet A -> isFinSet B
isFinSet-equiv {A = A} {B = B} eq = ∥-map handle
  where
  handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Σ[ n ∈ Nat ] (B ≃ Fin n)
  handle (n , eq-a) = n , (equiv⁻¹ eq >eq> eq-a)

-- Types with structure for finite sets.

FinSet : (ℓ : Level) -> Type (ℓ-suc ℓ)
FinSet ℓ = Σ[ t ∈ Type ℓ ] isFinSet t

FinSetΣ : (ℓ : Level) -> Type (ℓ-suc ℓ)
FinSetΣ ℓ = Σ[ t ∈ Type ℓ ] isFinSetΣ t

-- Cardnality of finite sets

cardnalityΣ : FinSetΣ ℓ -> Nat
cardnalityΣ (_ , (n , eq)) = n

cardnality : FinSet ℓ -> Nat
cardnality (A , fin) = cardnalityΣ (A , (isFinSet->isFinSetΣ fin))

cardnality-path : (A : FinSet ℓ) -> (finΣ : isFinSetΣ ⟨ A ⟩) -> cardnality A == ⟨ finΣ ⟩
cardnality-path (A , fin) finΣ = cong fst (isProp-isFinSetΣ (isFinSet->isFinSetΣ fin) finΣ)

-- Structures for implicit arguments
record FinSetStr (A : Type ℓ) : Type ℓ where
  field
    isFin : isFinSet A

-- Useful examples that aren't yet used.
private
  FinSet-LiftedFin-path' : (A : Type ℓ) (isFinA : isFinSetΣ A) -> ∥ A == Lift ℓ (Fin ⟨ isFinA ⟩) ∥
  FinSet-LiftedFin-path' {ℓ} A (n , eq) = ∥-map handle eq
    where
    handle : (A ≃ Fin n) -> A == Lift ℓ (Fin n)
    handle eq = ua (eq >eq> (equiv⁻¹ (liftEquiv ℓ (Fin n))))

  FinSet-LiftedFin-path : (A : FinSet ℓ) -> ∥ ⟨ A ⟩ == Lift ℓ (Fin (cardnality A)) ∥
  FinSet-LiftedFin-path (A , isFinA) = FinSet-LiftedFin-path' A (isFinSet->isFinSetΣ isFinA)

  extract : (A : FinSet ℓ) ->
            (f : Σ[ n ∈ Nat ] (⟨ A ⟩ ≃ Fin n) -> Nat) ->
            2-Constant f -> Nat
  extract (_ , finA) f f-const = ∥->Set isSetNat f f-const finA
