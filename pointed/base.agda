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


module _ {ℓA ℓB : Level} (A∙@(A , ★A) : Type∙ ℓA) (B∙@(B , ★B) : Type∙ ℓB) where
  _≃∙_ : Type (ℓ-max ℓA ℓB)
  _≃∙_ = Σ[ eq ∈ A ≃ B ] (eqFun eq ★A == ★B)

module _ {ℓ : Level} {A∙@(A , ★A) : Type∙ ℓ} {B∙@(B , ★B) : Type∙ ℓ} where
  Type∙-path : A∙ ≃∙ B∙ -> A∙ == B∙
  Type∙-path (eq , p) = \i -> tp i , ★p i
    where
    tp : A == B
    tp = ua eq
    ★p : PathP (\i -> tp i) ★A ★B
    ★p = ua-value-pathp eq _ _ p
