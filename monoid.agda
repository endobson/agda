{-# OPTIONS --cubical --safe --exact-split #-}

module monoid where

open import base
open import equality
open import functions
open import hlevel.base

record Monoid {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  infixl 6 _∙_

  field
    ε : Domain
    _∙_ : Domain -> Domain -> Domain
    ∙-assoc : {m n o : Domain} -> (m ∙ n) ∙ o == m ∙ (n ∙ o)
    ∙-left-ε : {m : Domain} -> (ε ∙ m) == m
    ∙-right-ε : {m : Domain} -> (m ∙ ε) == m
    isSet-Domain : isSet Domain

  ∙-right : {m n o : Domain} -> (n == o) -> m ∙ n == m ∙ o
  ∙-right {m} p i = m ∙ p i

  ∙-left : {m n o : Domain} -> (n == o) -> n ∙ m == o ∙ m
  ∙-left {m} p i = p i ∙ m


record Monoidʰᵉ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    (M₁ : Monoid D₁) (M₂ : Monoid D₂)
    (f : D₁ -> D₂) : Type (ℓ-max ℓ₁ ℓ₂)
    where
  module M₁ = Monoid M₁
  module M₂ = Monoid M₂

  field
    preserves-ε : f M₁.ε == M₂.ε
    preserves-∙ : ∀ x y -> f (x M₁.∙ y) == (f x) M₂.∙ (f y)

Monoidʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{M₁ : Monoid D₁}} {{M₂ : Monoid D₂}}
    (f : D₁ -> D₂)
    -> Type (ℓ-max ℓ₁ ℓ₂)
Monoidʰ {{M₁ = M₁}} {{M₂ = M₂}} f = Monoidʰᵉ M₁ M₂ f

module Monoidʰ {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {M₁ : Monoid D₁} {M₂ : Monoid D₂}
    {f : D₁ -> D₂}
    (cm : Monoidʰᵉ M₁ M₂ f) where
  open Monoidʰᵉ cm public


Monoidʰ-∘ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃}
  {M₁ : Monoid D₁} {M₂ : Monoid D₂} {M₃ : Monoid D₃}
  {f : D₂ -> D₃} {g : D₁ -> D₂}
  -> (Monoidʰᵉ M₂ M₃ f)
  -> (Monoidʰᵉ M₁ M₂ g)
  -> (Monoidʰᵉ M₁ M₃ (f ∘ g))
Monoidʰ-∘ {M₁ = M₁} {M₃ = M₃} {f = f} {g = g} f' g' = res
  where
  module M₁ = Monoid M₁
  module M₃ = Monoid M₃
  module f' = Monoidʰ f'
  module g' = Monoidʰ g'

  preserves-ε : (f ∘ g) M₁.ε == M₃.ε
  preserves-ε = (cong f g'.preserves-ε) >=> f'.preserves-ε

  preserves-∙ : ∀ x y -> (f ∘ g) (x M₁.∙ y) == ((f ∘ g) x) M₃.∙ ((f ∘ g) y)
  preserves-∙ x y = (cong f (g'.preserves-∙ x y)) >=> f'.preserves-∙ (g x) (g y)

  res : (Monoidʰᵉ M₁ M₃ (f ∘ g))
  res = record {
    preserves-ε = preserves-ε ;
    preserves-∙ = preserves-∙
    }

module _
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {M₁ : Monoid D₁} {M₂ : Monoid D₂}
    {f : D₁ -> D₂}
    where
  private
    isSetD = Monoid.isSet-Domain M₂
  abstract
    isProp-Monoidʰ : isProp (Monoidʰᵉ M₁ M₂ f)
    isProp-Monoidʰ h1 h2 i .Monoidʰ.preserves-ε =
      isSetD _ _ (Monoidʰ.preserves-ε h1) (Monoidʰ.preserves-ε h2) i
    isProp-Monoidʰ h1 h2 i .Monoidʰ.preserves-∙ x y =
      isSetD _ _ (Monoidʰ.preserves-∙ h1 x y) (Monoidʰ.preserves-∙ h2 x y) i

MonoidT : (ℓ : Level) -> Type (ℓ-suc ℓ)
MonoidT ℓ = Σ[ D ∈ Type ℓ ] (Monoid D)
