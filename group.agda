{-# OPTIONS --cubical --safe --exact-split #-}

module group where

open import base
open import equality
open import functions
open import commutative-monoid

record GroupStr {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    comm-monoid : CommMonoid Domain
  open CommMonoid comm-monoid public

  field
    inverse : Domain -> Domain
    ∙-left-inverse : {x : Domain} -> (inverse x) ∙ x == ε

  ∙-right-inverse : {x : Domain} -> x ∙ (inverse x) == ε
  ∙-right-inverse = ∙-commute >=> ∙-left-inverse

Group : (ℓ : Level) -> Type (ℓ-suc ℓ)
Group ℓ = Σ[ D ∈ Type ℓ ] (GroupStr D)


record Groupʰᵉ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    (G₁ : GroupStr D₁) (G₂ : GroupStr D₂)
    (f : D₁ -> D₂) : Type (ℓ-max ℓ₁ ℓ₂)
    where
  module G₁ = GroupStr G₁
  module G₂ = GroupStr G₂

  field
    preserves-ε : f G₁.ε == G₂.ε
    preserves-∙ : ∀ x y -> f (x G₁.∙ y) == (f x) G₂.∙ (f y)
    preserves-inverse : ∀ x -> f (G₁.inverse x) == (G₂.inverse (f x))

Groupʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{G₁ : GroupStr D₁}} {{G₂ : GroupStr D₂}}
    (f : D₁ -> D₂)
    -> Type (ℓ-max ℓ₁ ℓ₂)
Groupʰ {{G₁ = G₁}} {{G₂ = G₂}} f = Groupʰᵉ G₁ G₂ f

module Groupʰ {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {G₁ : GroupStr D₁} {G₂ : GroupStr D₂}
    {f : D₁ -> D₂}
    (cm : Groupʰᵉ G₁ G₂ f) where
  open Groupʰᵉ cm public
