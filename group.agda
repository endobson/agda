{-# OPTIONS --cubical --safe --exact-split #-}

module group where

open import base
open import commutative-monoid
open import equality
open import functions
open import hlevel.base
open import monoid

record GroupStr {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    monoid : Monoid Domain
  open Monoid monoid public

  field
    inverse : Domain -> Domain
    ∙-left-inverse : {x : Domain} -> (inverse x) ∙ x == ε
    ∙-right-inverse : {x : Domain} -> x ∙ (inverse x) == ε

record AbGroupStr {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    comm-monoid : CommMonoid Domain
  open CommMonoid comm-monoid public

  field
    inverse : Domain -> Domain
    ∙-left-inverse : {x : Domain} -> (inverse x) ∙ x == ε
    ∙-right-inverse : {x : Domain} -> x ∙ (inverse x) == ε

  abstract
    inverse-CMʰ : CommMonoidʰᵉ comm-monoid comm-monoid inverse
    inverse-CMʰ = record
      { monoidʰ = record
        { preserves-ε = sym ∙-right-ε >=> ∙-left-inverse
        ; preserves-∙ = preserves-∙
        }
      }
      where
      preserves-∙ : (x y : Domain) -> inverse (x ∙ y) == (inverse x) ∙ (inverse y)
      preserves-∙ x y =
        sym ∙-right-ε >=>
        ∙-right (sym ∙-right-ε >=>
                 cong2 _∙_ (sym ∙-right-inverse) (sym ∙-right-inverse) >=>
                 ∙-assoc >=>
                 ∙-right (sym ∙-assoc >=> ∙-left ∙-commute >=> ∙-assoc) >=>
                 sym ∙-assoc) >=>
        sym ∙-assoc >=>
        ∙-left ∙-left-inverse >=>
        ∙-left-ε

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

opaque
  isProp-Groupʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {G₁ : GroupStr D₁} {G₂ : GroupStr D₂}
    {f : D₁ -> D₂} -> isProp (Groupʰᵉ G₁ G₂ f)
  isProp-Groupʰ {D₁ = D₁} {D₂} {G₁} {G₂} h₁ h₂ i = record
    { preserves-ε = isSet-D₂ _ _ h₁.preserves-ε h₂.preserves-ε i
    ; preserves-∙ = \x y -> isSet-D₂ _ _ (h₁.preserves-∙ x y) (h₂.preserves-∙ x y) i
    ; preserves-inverse = \x -> isSet-D₂ _ _ (h₁.preserves-inverse x) (h₂.preserves-inverse x) i
    }
    where
    module h₁ = Groupʰ h₁
    module h₂ = Groupʰ h₂

    isSet-D₂ : isSet D₂
    isSet-D₂ = GroupStr.isSet-Domain G₂

  Groupʰ-∘ :
    {ℓ₁ ℓ₂ ℓ₃ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃}
    {G₁ : GroupStr D₁} {G₂ : GroupStr D₂} {G₃ : GroupStr D₃}
    {f : D₂ -> D₃} {g : D₁ -> D₂} ->
    (Groupʰᵉ G₂ G₃ f) -> (Groupʰᵉ G₁ G₂ g) -> (Groupʰᵉ G₁ G₃ (f ∘ g))
  Groupʰ-∘ {f = f} {g = g} f' g' = record
    { preserves-ε = (cong f g'.preserves-ε) >=> f'.preserves-ε
    ; preserves-∙ = \x y -> (cong f (g'.preserves-∙ x y)) >=> f'.preserves-∙ (g x) (g y)
    ; preserves-inverse = \x -> cong f (g'.preserves-inverse x) >=> f'.preserves-inverse (g x)
    }
    where
    module f' = Groupʰ f'
    module g' = Groupʰ g'

module _ {ℓ : Level} ((D , G) : Group ℓ) where
  private
    module G = GroupStr G

  record isAbelian  : Type ℓ where
    field
      ∙-commute : ∀ (a b : D) -> a G.∙ b == b G.∙ a
