{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.base where

open import base
open import equality-path
open import equivalence
open import functions
open import univalence

Type∙ : (ℓ : Level) -> Type (ℓ-suc ℓ)
Type∙ ℓ = Σ[ X ∈ Type ℓ ] X

module _ {ℓA ℓB : Level} ((A , ★A) : Type∙ ℓA) ((B , ★B) : Type∙ ℓB) where
  record _->∙_ : Type (ℓ-max ℓA ℓB) where
    constructor ->∙-cons
    field
      f : A -> B
      preserves-★ : f ★A == ★B

  _->∙∙_ : Type∙ (ℓ-max ℓA ℓB)
  _->∙∙_ = _->∙_ , ->∙-cons (\_ -> ★B) refl

module _ {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB} where
  app∙ : (A∙ ->∙ B∙) -> A -> B
  app∙ (->∙-cons f _) = f
  ->∙-path : (f : A∙ ->∙ B∙) -> app∙ f ★A == ★B
  ->∙-path (->∙-cons _ p) = p

_>∙>_ : {ℓA ℓB ℓC : Level} {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} {C∙ : Type∙ ℓC} ->
        (A∙ ->∙ B∙) -> (B∙ ->∙ C∙) -> (A∙ ->∙ C∙)
(->∙-cons f₁ p₁) >∙> (->∙-cons f₂ p₂) =
  (->∙-cons (f₂ ∘ f₁) (cong f₂ p₁ >=> p₂))

const->∙ : {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB} -> (A∙ ->∙ B∙)
const->∙ = ->∙-cons _ refl


module _ {ℓA ℓB : Level} (A∙@(A , ★A) : Type∙ ℓA) (B∙@(B , ★B) : Type∙ ℓB) where
  _≃∙_ : Type (ℓ-max ℓA ℓB)
  _≃∙_ = Σ[ eq ∈ A ≃ B ] (eqFun eq ★A == ★B)

module _ {ℓA ℓB ℓC : Level}
         {A∙@(A , ★A) : Type∙ ℓA}
         {B∙@(B , ★B) : Type∙ ℓB}
         {C∙@(C , ★C) : Type∙ ℓC}
         where
  _>≃∙>_ : A∙ ≃∙ B∙ -> B∙ ≃∙ C∙ -> A∙ ≃∙ C∙
  _>≃∙>_ (eq₁ , p₁) (eq₂ , p₂) = (eq₁ >eq> eq₂) , cong (eqFun eq₂) p₁ >=> p₂

equiv∙⁻¹ : {ℓA ℓB : Level} {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} -> (A∙ ≃∙ B∙) -> (B∙ ≃∙ A∙)
equiv∙⁻¹ (eq , p) = equiv⁻¹ eq , cong (eqInv eq) (sym p) >=> eqRet eq _

module _ {ℓ : Level} {A∙@(A , ★A) : Type∙ ℓ} {B∙@(B , ★B) : Type∙ ℓ} where
  Type∙-path : A∙ ≃∙ B∙ -> A∙ == B∙
  Type∙-path (eq , p) = \i -> tp i , ★p i
    where
    tp : A == B
    tp = ua eq
    ★p : PathP (\i -> tp i) ★A ★B
    ★p = ua-value-pathp eq _ _ p


module _ {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB}
  where
  fiber∙ : (A∙ ->∙ B∙) -> Type∙ (ℓ-max ℓA ℓB)
  fiber∙ (->∙-cons f fp) = fiber f ★B , (★A , fp)


Top∙ : Type∙ ℓ-zero
Top∙ = Top , tt


Σ∙ : {ℓA ℓB : Level} -> (A∙@(A , ★A) : Type∙ ℓA) -> (B : A -> Type ℓB) -> B ★A -> Type∙ (ℓ-max ℓA ℓB)
Σ∙ (A , ★A) B ★B = (Σ A B) , (★A , ★B)
