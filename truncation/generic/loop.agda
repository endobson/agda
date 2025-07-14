{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.generic.loop where

open import base
open import univalence
open import equality-path
open import isomorphism hiding (iso)
open import equivalence
open import sigma.base
open import pointed.base
open import pointed.loop-space
open import truncation.generic
open import truncation.generic.path

module _ {ℓA ℓB : Level} (A∙@(A , ★A) : Type∙ ℓA) (B∙@(B , ★B) : Type∙ ℓB) where
  record Iso∙ : Type (ℓ-max ℓA ℓB) where
    constructor iso∙
    field
      fun : A -> B
      inv : B -> A
      rightInv : ∀ b -> fun (inv b) == b
      leftInv : ∀ a -> inv (fun a) == a
      preserves-∙ : fun ★A == ★B

    iso : Iso A B
    iso = isomorphism.iso fun inv rightInv leftInv
      

module _ {ℓ : Level} {A∙@(A , ★A) : Type∙ ℓ} {B∙@(B , ★B) : Type∙ ℓ} where
  iso∙ToPath : Iso∙ A∙ B∙ -> A∙ == B∙
  iso∙ToPath i∙ = 
    Σ-path 
      (isoToPath (Iso∙.iso i∙)) 
      (transP-left (isoToPath-filler (Iso∙.iso i∙) ★A) (Iso∙.preserves-∙ i∙))

module _ {ℓ : Level} (n : Nat) (A∙@(A , ★A) : Type∙ ℓ) where
  squashed-loop-path : (Squashₙ∙ n (Ω A∙)) == Ω (Squashₙ∙ (suc n) A∙)
  squashed-loop-path = 
    iso∙ToPath (iso∙ (eqFun eq) (eqInv eq) (eqSec eq) (eqRet eq)
                     (squashed-path-eq-refl n ★A))
    where
    eq : ⟨ Squashₙ∙ n (Ω A∙) ⟩ ≃ ⟨ Ω (Squashₙ∙ (suc n) A∙) ⟩
    eq = squashed-path-eq n ★A ★A
