{-# OPTIONS --cubical --safe --exact-split #-}

module order.homomorphism where

open import base
open import order
open import hlevel.base

record LinearOrderʰᵉ
  {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  (O₁ : LinearOrderStr D₁ ℓ<₁) (O₂ : LinearOrderStr D₂ ℓ<₂)
  (f : D₁ -> D₂) : Type (ℓ-max* 4 ℓD₁ ℓD₂ (ℓ-suc ℓ<₁) (ℓ-suc ℓ<₂))
  where
  private
    _<₁_ = LinearOrderStr._<_ O₁
    _<₂_ = LinearOrderStr._<_ O₂

  field
    preserves-< : ∀ {x y} -> x <₁ y -> f x <₂ f y

LinearOrderʰ :
  {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {{ O₁ : LinearOrderStr D₁ ℓ<₁ }} {{ O₂ : LinearOrderStr D₂ ℓ<₂ }}
  (f : D₁ -> D₂) ->
  Type (ℓ-max* 4 ℓD₁ ℓD₂ (ℓ-suc ℓ<₁) (ℓ-suc ℓ<₂))
LinearOrderʰ {{O₁ = O₁}} {{O₂ = O₂}} f = LinearOrderʰᵉ O₁ O₂ f

isProp-LinearOrderʰ :
  {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
  {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
  {O₁ : LinearOrderStr D₁ ℓ<₁} {O₂ : LinearOrderStr D₂ ℓ<₂}
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
  {O₁ : LinearOrderStr D₁ ℓ<₁} {O₂ : LinearOrderStr D₂ ℓ<₂}
  {f : D₁ -> D₂} (h : LinearOrderʰᵉ O₁ O₂ f)
  where
  open LinearOrderʰᵉ h public
