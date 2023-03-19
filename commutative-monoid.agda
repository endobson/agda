{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid where

open import base
open import equality
open import functions
open import hlevel
open import monoid

record CommMonoid {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    {{monoid}} : monoid.Monoid Domain
  open monoid.Monoid monoid public

  field
    ∙-commute : {m n : Domain} -> (m ∙ n) == (n ∙ m)

record CommMonoidʰᵉ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    (M₁ : CommMonoid D₁) (M₂ : CommMonoid D₂)
    (f : D₁ -> D₂) : Type (ℓ-max ℓ₁ ℓ₂)
    where
  module M₁ = CommMonoid M₁
  module M₂ = CommMonoid M₂

  field
    monoidʰ : monoid.Monoidʰᵉ M₁.monoid M₂.monoid f

  preserves-ε : f M₁.ε == M₂.ε
  preserves-ε = Monoidʰ.preserves-ε monoidʰ
  preserves-∙ : ∀ x y -> f (x M₁.∙ y) == (f x) M₂.∙ (f y)
  preserves-∙ = Monoidʰ.preserves-∙ monoidʰ

CommMonoidʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{M₁ : CommMonoid D₁}} {{M₂ : CommMonoid D₂}}
    (f : D₁ -> D₂)
    -> Type (ℓ-max ℓ₁ ℓ₂)
CommMonoidʰ {{M₁ = M₁}} {{M₂ = M₂}} f = CommMonoidʰᵉ M₁ M₂ f

module CommMonoidʰ {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {M₁ : CommMonoid D₁} {M₂ : CommMonoid D₂}
    {f : D₁ -> D₂}
    (cm : CommMonoidʰᵉ M₁ M₂ f) where
  open CommMonoidʰᵉ cm public

CommMonoidʰ-∘ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃}
  {M₁ : CommMonoid D₁} {M₂ : CommMonoid D₂} {M₃ : CommMonoid D₃}
  {f : D₂ -> D₃} {g : D₁ -> D₂}
  -> (CommMonoidʰᵉ M₂ M₃ f)
  -> (CommMonoidʰᵉ M₁ M₂ g)
  -> (CommMonoidʰᵉ M₁ M₃ (f ∘ g))
CommMonoidʰ-∘ f g = record
    { monoidʰ = Monoidʰ-∘ f.monoidʰ g.monoidʰ
    }
  where
  module f = CommMonoidʰ f
  module g = CommMonoidʰ g

module _
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {M₁ : CommMonoid D₁} {M₂ : CommMonoid D₂}
    {f : D₁ -> D₂}
    where
  abstract
    isProp-CommMonoidʰ : isProp (CommMonoidʰᵉ M₁ M₂ f)
    isProp-CommMonoidʰ h1 h2 i .CommMonoidʰ.monoidʰ =
      isProp-Monoidʰ (CommMonoidʰ.monoidʰ h1) (CommMonoidʰ.monoidʰ h2) i

CommMonoidT : (ℓ : Level) -> Type (ℓ-suc ℓ)
CommMonoidT ℓ = Σ[ D ∈ Type ℓ ] (CommMonoid D)
