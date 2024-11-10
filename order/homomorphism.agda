{-# OPTIONS --cubical --safe --exact-split #-}

module order.homomorphism where

open import base
open import order
open import equality
open import functions
open import relation
open import hlevel.base

record LinearOrderʰᵉ
  {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {_<₁_ : Rel D₁ ℓ<₁} {_<₂_ : Rel D₂ ℓ<₂}
  (O₁ : isLinearOrder _<₁_) (O₂ : isLinearOrder _<₂_)
  (f : D₁ -> D₂) : Type (ℓ-max* 4 ℓD₁ ℓD₂ ℓ<₁ ℓ<₂)
  where

  field
    preserves-< : ∀ {x y} -> x <₁ y -> f x <₂ f y

  injective : isInjective f
  injective fx=fy =
    connected-< (\x<y -> irrefl-path-< fx=fy (preserves-< x<y))
                (\y<x -> irrefl-path-< (sym fx=fy) (preserves-< y<x))
    where
    instance
      IO₁ = O₁
      IO₂ = O₂

  reflects-< : {{ DO : DecidableLinearOrderStr O₁}} {x y : D₁} -> f x <₂ f y -> x <₁ y
  reflects-< {x} {y} fx<fy = handle (trichotomous-< x y)
    where
    instance
      IO₁ = O₁
      IO₂ = O₂

    handle : Tri< x y -> x < y
    handle (tri< x<y _ _) = x<y
    handle (tri= _ x=y _) = bot-elim (irrefl-path-< (cong f x=y) fx<fy)
    handle (tri> _ _ y<x) = bot-elim (asym-< (preserves-< y<x) fx<fy)

LinearOrderʰ :
  {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {_<₁_ : Rel D₁ ℓ<₁} {_<₂_ : Rel D₂ ℓ<₂}
  {{O₁ : isLinearOrder _<₁_}} {{O₂ : isLinearOrder _<₂_}}
  (f : D₁ -> D₂) ->
  Type (ℓ-max* 4 ℓD₁ ℓD₂ ℓ<₁ ℓ<₂)
LinearOrderʰ {{O₁ = O₁}} {{O₂ = O₂}} f = LinearOrderʰᵉ O₁ O₂ f

isProp-LinearOrderʰ :
  {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {_<₁_ : Rel D₁ ℓ<₁} {_<₂_ : Rel D₂ ℓ<₂}
  {O₁ : isLinearOrder _<₁_} {O₂ : isLinearOrder _<₂_}
  {f : D₁ -> D₂} ->
  isProp (LinearOrderʰᵉ O₁ O₂ f)
isProp-LinearOrderʰ {O₂ = O₂} h1 h2 i .LinearOrderʰᵉ.preserves-< lt =
  isProp-< (h1.preserves-< lt) (h2.preserves-< lt) i
  where
  module h1 = LinearOrderʰᵉ h1
  module h2 = LinearOrderʰᵉ h2
  instance
    IO₂ = O₂

module LinearOrderʰ
  {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {_<₁_ : Rel D₁ ℓ<₁} {_<₂_ : Rel D₂ ℓ<₂}
  {O₁ : isLinearOrder _<₁_} {O₂ : isLinearOrder _<₂_}
  {f : D₁ -> D₂} (h : LinearOrderʰᵉ O₁ O₂ f)
  where
  open LinearOrderʰᵉ h public

LinearOrderʰ-∘ :
  {ℓD₁ ℓD₂ ℓD₃ ℓ<₁ ℓ<₂ ℓ<₃ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂} {D₃ : Type ℓD₃}
  {_<₁_ : Rel D₁ ℓ<₁} {_<₂_ : Rel D₂ ℓ<₂} {_<₃_ : Rel D₃ ℓ<₃}
  {O₁ : isLinearOrder _<₁_} {O₂ : isLinearOrder _<₂_} {O₃ : isLinearOrder _<₃_}
  {f₁₂ : D₁ -> D₂} {f₂₃ : D₂ -> D₃}
  (h₁₂ : LinearOrderʰᵉ O₁ O₂ f₁₂) (h₂₃ : LinearOrderʰᵉ O₂ O₃ f₂₃) ->
  LinearOrderʰᵉ O₁ O₃ (f₂₃ ∘ f₁₂)
LinearOrderʰ-∘ h₁₂ h₂₃ = record { preserves-< = h₂₃.preserves-< ∘ h₁₂.preserves-< }
  where
  module h₁₂ = LinearOrderʰ h₁₂
  module h₂₃ = LinearOrderʰ h₂₃


record PartialOrderʰᵉ
  {ℓD₁ ℓD₂ ℓ≤₁ ℓ≤₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  (O₁ : PartialOrderStr D₁ ℓ≤₁) (O₂ : PartialOrderStr D₂ ℓ≤₂)
  (f : D₁ -> D₂) : Type (ℓ-max* 4 ℓD₁ ℓD₂ (ℓ-suc ℓ≤₁) (ℓ-suc ℓ≤₂))
  where
  private
    _≤₁_ = PartialOrderStr._≤_ O₁
    _≤₂_ = PartialOrderStr._≤_ O₂

  field
    preserves-≤ : ∀ {x y} -> x ≤₁ y -> f x ≤₂ f y

PartialOrderʰ :
  {ℓD₁ ℓD₂ ℓ≤₁ ℓ≤₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {{ O₁ : PartialOrderStr D₁ ℓ≤₁ }} {{ O₂ : PartialOrderStr D₂ ℓ≤₂ }}
  (f : D₁ -> D₂) ->
  Type (ℓ-max* 4 ℓD₁ ℓD₂ (ℓ-suc ℓ≤₁) (ℓ-suc ℓ≤₂))
PartialOrderʰ {{O₁ = O₁}} {{O₂ = O₂}} f = PartialOrderʰᵉ O₁ O₂ f


module PartialOrderʰ
  {ℓD₁ ℓD₂ ℓ≤₁ ℓ≤₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {O₁ : PartialOrderStr D₁ ℓ≤₁} {O₂ : PartialOrderStr D₂ ℓ≤₂}
  {f : D₁ -> D₂} (h : PartialOrderʰᵉ O₁ O₂ f)
  where
  open PartialOrderʰᵉ h public
