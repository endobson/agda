{-# OPTIONS --cubical --safe --exact-split #-}

module functions where

open import base
open import cubical
open import relation
open import equality-path

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Type ℓ

infixr 9 _∘_

_∘_ : {A : Type ℓ₁} {B : Type ℓ₂} {C : (b : B) -> Type ℓ₃} (f : (b : B) -> (C b))
      (g : A -> B) -> (a : A) -> C (g a)
(f ∘ g) a = f (g a)

isComposition : (f : B -> C) (g : A -> B) (h : A -> C) -> Type _
isComposition f g h = ∀ a -> f (g a) == h a

Injective : Pred (A -> B) _
Injective f = ∀ {a1 a2} -> (f a1) == (f a2) -> a1 == a2

∘-Injective : {f : B -> C} {g : A -> B} -> Injective f -> Injective g -> Injective (f ∘ g)
∘-Injective fi gi = gi ∘ fi

∘-Injective⁻ : (f : B -> C) (g : A -> B) -> Injective (f ∘ g) -> Injective g
∘-Injective⁻ f g fgi p = fgi (cong f p)

Injective2 : Pred (A -> B -> C) _
Injective2 f = ∀ {a1 b1 a2 b2} -> (f a1 b1) == (f a2 b2) -> (a1 == a2) × (b1 == b2)

Monotonic : Rel A ℓ₁ -> Rel B ℓ₂ -> Pred (A -> B) _
Monotonic {A = A} {B = B} _≤a_ _≤b_ f = ∀ a1 a2 -> a1 ≤a a2 -> (f a1) ≤b (f a2)

RightInverse : (A -> B) -> Pred (B -> A) _
RightInverse f g = ∀ b -> f (g b) == b

LeftInverse : (A -> B) -> Pred (B -> A) _
LeftInverse f g = ∀ b -> (g (f b)) == b

Involution : Pred (A -> A) _
Involution f = ∀ {a} -> (f (f a)) == a

-- Constant functions.
-- 2-Constant is constant up to paths.
2-Constant : (A -> B) -> Type _
2-Constant {A = A} f = (x y : A) -> f x == f y

isEmbedding : Pred (A -> B) _
isEmbedding f = ∀ x y -> isEquiv {A = x == y} (cong f)

isSectionOf : (f : A -> B) -> Pred (B -> A) _
isSectionOf f g = ∀ b -> f ( g b) == b

isRetractionOf : (f : A -> B) -> Pred (B -> A) _
isRetractionOf f g = ∀ b -> g (f b) == b

Section : Pred (A -> B) _
Section {A = A} {B = B} f = Σ (B -> A) (isSectionOf f)

Retraction : Pred (A -> B) _
Retraction {A = A} {B = B} f = Σ (B -> A) (isRetractionOf f)
