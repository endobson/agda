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

module Group {ℓ : Level} (G : Group ℓ) where
  open GroupStr (snd G) public

  Domain : Type ℓ
  Domain = ⟨ G ⟩

  D : Type ℓ
  D = Domain

module _ {ℓ₁ ℓ₂ : Level}
         (G₁@(D₁ , GS₁) : Group ℓ₁)
         (G₂@(D₂ , GS₂) : Group ℓ₂)
  where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂

  record isGroupʰ (f : G₁.D -> G₂.D) : Type (ℓ-max ℓ₁ ℓ₂) where
    field
      preserves-ε : f G₁.ε == G₂.ε
      preserves-∙ : ∀ x y -> f (x G₁.∙ y) == (f x) G₂.∙ (f y)
      preserves-inverse : ∀ x -> f (G₁.inverse x) == (G₂.inverse (f x))


  Groupʰ : Type (ℓ-max ℓ₁ ℓ₂)
  Groupʰ = Σ (G₁.D -> G₂.D) isGroupʰ


module Groupʰ {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂}
              (h : Groupʰ G₁ G₂) where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂

  open isGroupʰ (snd h) public

  f : G₁.D -> G₂.D
  f = fst h


module _ {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂} where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂

  opaque
    isProp-isGroupʰ : {f : G₁.D -> G₂.D} -> isProp (isGroupʰ G₁ G₂ f)
    isProp-isGroupʰ h₁ h₂ i = record
      { preserves-ε = isSet-D₂ _ _ h₁.preserves-ε h₂.preserves-ε i
      ; preserves-∙ = \x y -> isSet-D₂ _ _ (h₁.preserves-∙ x y) (h₂.preserves-∙ x y) i
      ; preserves-inverse = \x -> isSet-D₂ _ _ (h₁.preserves-inverse x) (h₂.preserves-inverse x) i
      }
      where
      module h₁ = isGroupʰ h₁
      module h₂ = isGroupʰ h₂

      isSet-D₂ : isSet G₂.D
      isSet-D₂ = G₂.isSet-Domain

module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂} {G₃ : Group ℓ₂} where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂
    module G₃ = Group G₃

  ∘-isGroupʰ :
    {f : G₂.D -> G₃.D} {g : G₁.D -> G₂.D} ->
    (isGroupʰ G₂ G₃ f) -> (isGroupʰ G₁ G₂ g) -> (isGroupʰ G₁ G₃ (f ∘ g))
  ∘-isGroupʰ {f = f} {g = g} fʰ gʰ = record
    { preserves-ε = (cong f gʰ.preserves-ε) >=> fʰ.preserves-ε
    ; preserves-∙ = \x y -> (cong f (gʰ.preserves-∙ x y)) >=> fʰ.preserves-∙ (g x) (g y)
    ; preserves-inverse = \x -> cong f (gʰ.preserves-inverse x) >=> fʰ.preserves-inverse (g x)
    }
    where
    module fʰ = isGroupʰ fʰ
    module gʰ = isGroupʰ gʰ

  ∘-Groupʰ : (Groupʰ G₂ G₃) -> (Groupʰ G₁ G₂) -> (Groupʰ G₁ G₃)
  ∘-Groupʰ (f , fʰ) (g , gʰ) = f ∘ g , ∘-isGroupʰ fʰ gʰ

  _>Groupʰ>_ : (Groupʰ G₁ G₂) -> (Groupʰ G₂ G₃) -> (Groupʰ G₁ G₃)
  f >Groupʰ> g = ∘-Groupʰ g f


module _ {ℓ : Level} (G : Group ℓ) where
  private
    module G = Group G

  record isAbelian  : Type ℓ where
    field
      ∙-commute : ∀ (a b : G.D) -> a G.∙ b == b G.∙ a
