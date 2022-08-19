{-# OPTIONS --cubical --safe --exact-split #-}

module finitely-indexed where

open import base
open import cubical
open import equality
open import equivalence
open import fin-algebra
open import fin
open import finset
open import finset.instances
open import functions
open import hlevel
open import isomorphism
open import truncation

private
  variable
    ℓ : Level
    A : Type ℓ

isKFinSetΣ : Type ℓ -> (ℓ₂ : Level) -> Type (ℓ-max ℓ (ℓ-suc ℓ₂))
isKFinSetΣ A ℓ₂ = Σ[ B ∈ (FinSet ℓ₂) ] (Σ (⟨ B ⟩ -> A) isSurjection)

isKFinSetΣ⁻ : Type ℓ -> Type ℓ
isKFinSetΣ⁻ A = Σ[ n ∈ Nat ] (Σ (Fin n -> A) isSurjection)

isKFinSet : Type ℓ -> (ℓ₂ : Level) -> Type (ℓ-max ℓ (ℓ-suc ℓ₂))
isKFinSet A ℓ = ∥ isKFinSetΣ A ℓ ∥

isKFinSet⁻ : Type ℓ -> Type ℓ
isKFinSet⁻ A = ∥ isKFinSetΣ⁻ A ∥

KFinSet : (ℓ₁ ℓ₂ : Level) -> Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
KFinSet ℓ₁ ℓ₂ = Σ[ A ∈ (Type ℓ₁) ] (isKFinSet A ℓ₂)

KFinSet⁻ : (ℓ₁ : Level) -> Type (ℓ-suc ℓ₁)
KFinSet⁻ ℓ₁  = Σ[ A ∈ (Type ℓ₁) ] (isKFinSet⁻ A)

KFinListing' : Type ℓ -> (ℓ₂ : Level) -> Type (ℓ-max ℓ (ℓ-suc ℓ₂))
KFinListing' A ℓ₂ = Σ[ B ∈ (FinSet ℓ₂) ] (∃ (⟨ B ⟩ -> A) isSurjection)

isIndexable : Type ℓ -> Nat -> Type ℓ 
isIndexable A n = ∃ (FinT n -> A) isSurjection

isListableΣ : Type ℓ -> Type ℓ 
isListableΣ A = Σ Nat (isIndexable A)

isListable : Type ℓ -> Type ℓ 
isListable A = ∥ isListableΣ A ∥

--

isKFinSet⁻-eq : {ℓ₂ : Level} {A : Type ℓ} -> isKFinSet⁻ A ≃ isKFinSet A ℓ₂
isKFinSet⁻-eq {A = A} = isoToEquiv (isProp->iso g f squash squash)
  where
  f : isKFinSet A _ -> isKFinSet⁻ A
  f bfs = ∥-bind handle bfs
    where
    handle : isKFinSetΣ A _ -> isKFinSet⁻ A
    handle ((B , fsB) , (f , sur-f)) = ∥-map handle2 fsB
      where
      handle2 : Σ[ n ∈ Nat ] (B ≃ Fin n) -> isKFinSetΣ⁻ A
      handle2 (n , eqB) = 
        n , f ∘ eqInv eqB , 
        (\b -> ∥-map (\{(i , p) -> eqFun eqB i , cong f (eqRet eqB i) >=> p}) (sur-f b))


  g : isKFinSet⁻ A -> isKFinSet A _
  g bfs = ∥-map handle bfs
    where
    handle : isKFinSetΣ⁻ A -> isKFinSetΣ A _
    handle (n , f , sur-f) = 
      FinSet-Lift _ (FinSet-Fin n) , f ∘ Lift.lower ,
      (\b -> ∥-map (\x -> _ , (snd x)) (sur-f b))


isZeroIndexable-eq : isIndexable A 0 -> A ≃ Bot
isZeroIndexable-eq {A = A} idx-A = isoToEquiv (isProp->iso f bot-elim isProp-A isPropBot)
  where
  f : A -> Bot
  f a = unsquash isPropBot (∥-bind (\{(_ , sur-g) -> ∥-map fst (sur-g a)}) idx-A)

  isProp-A : isProp A
  isProp-A a = bot-elim (f a)
