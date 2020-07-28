{-# OPTIONS --cubical --safe --exact-split #-}

module functions where

open import base
open import relation
open import equality

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Type ℓ

infixr 9 _∘_

_∘_ : {A : Type ℓ₁} {B : Type ℓ₂} {C : (b : B) -> Type ℓ₃} (f : (b : B) -> (C b))
      (g : A -> B) -> (a : A) -> C (g a)
(f ∘ g) a = f (g a)

Injective : Pred (A -> B) _
Injective f = ∀ {a1 a2} -> (f a1) == (f a2) -> a1 == a2

Injective2 : Pred (A -> B -> C) _
Injective2 f = ∀ {a1 b1 a2 b2} -> (f a1 b1) == (f a2 b2) -> (a1 == a2) × (b1 == b2)
