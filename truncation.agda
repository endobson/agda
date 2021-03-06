{-# OPTIONS --cubical --safe --exact-split #-}

module truncation where

open import base
open import equality
open import functions
open import hlevel

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
    A B C : Type ℓ

data Squash (A : Type ℓ) : Type ℓ where
  ∣_∣ : A -> Squash A
  squash : (a b : Squash A) -> a == b

∥_∥ : Type ℓ -> Type ℓ
∥_∥ = Squash

unsquash : isProp A -> ∥ A ∥ -> A
unsquash h ∣ a ∣ = a
unsquash h (squash a b i) = h (unsquash h a) (unsquash h b) i

∥-map : (A -> B) -> ∥ A ∥ -> ∥ B ∥
∥-map f ∣ a ∣ = ∣ f a ∣
∥-map f (squash a1 a2 i) = (squash (∥-map f a1) (∥-map f a2) i)

private
  module rec (BSet : isSet B) where
    ∥->Set       : (f : A -> B) (eq : 2-Constant f) -> ∥ A ∥ -> B
    ∥->SetHelper : (f : A -> B) (eq : 2-Constant f) (x y : ∥ A ∥) -> ∥->Set f eq x == ∥->Set f eq y

    ∥->Set f _  ∣ x ∣          = f x
    ∥->Set f eq (squash x y i) = ∥->SetHelper f eq x y i
    ∥->SetHelper f eq (squash x1 x2 i) y =
      isSet->Squareᵉ BSet
        (∥->SetHelper f eq x1 y)
        (∥->SetHelper f eq x2 y)
        (∥->SetHelper f eq x1 x2)
        refl
        i
    ∥->SetHelper f eq x@(∣ _ ∣) (squash y1 y2 i) =
      isSet->Squareᵉ BSet
        (∥->SetHelper f eq x y1)
        (∥->SetHelper f eq x y2)
        refl
        (∥->SetHelper f eq y1 y2)
        i
    ∥->SetHelper f eq ∣ x ∣ ∣ y ∣ = eq x y

open rec public using (∥->Set)

-- Mere existence

∃ : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃ A B = ∥ Σ A B ∥

infix 2 ∃-syntax

∃-syntax : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
