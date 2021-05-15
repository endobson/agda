{-# OPTIONS --cubical --safe --exact-split #-}

module isomorphism.base where

open import base

private
  variable
    ℓ : Level
    A B C : Type ℓ

private
  section : (f : A -> B) (g : B -> A) -> Type _
  section f g = ∀ b -> f (g b) == b

  retract : (f : A -> B) (g : B -> A) -> Type _
  retract f g = ∀ a -> g (f a) == a

record Iso {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor iso
  field
    fun : A -> B
    inv : B -> A
    rightInv : section fun inv
    leftInv : retract fun inv
