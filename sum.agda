{-# OPTIONS --cubical --safe --exact-split #-}

module sum where

open import base
open import equality
open import hlevel.base
open import isomorphism

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C D : Type ℓ

open Iso

⊎-map : (A -> C) -> (B -> D) -> (A ⊎ B) -> (C ⊎ D)
⊎-map f g (inj-l a) = inj-l (f a)
⊎-map f g (inj-r b) = inj-r (g b)

⊎-iso : ∀ {ℓ} {A B C D : Type ℓ} -> Iso A C -> Iso B D -> Iso (A ⊎ B) (C ⊎ D)
(⊎-iso f g) .fun = ⊎-map (f .fun) (g .fun)
(⊎-iso f g) .inv = ⊎-map (f .inv) (g .inv)
(⊎-iso f g) .rightInv (inj-l c) = cong inj-l (f .rightInv c)
(⊎-iso f g) .rightInv (inj-r d) = cong inj-r (g .rightInv d)
(⊎-iso f g) .leftInv  (inj-l a) = cong inj-l (f .leftInv a)
(⊎-iso f g) .leftInv  (inj-r b) = cong inj-r (g .leftInv b)

Left : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> A ⊎ B -> Type₀
Left (inj-l _) = Top
Left (inj-r _) = Bot

Right : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> A ⊎ B -> Type₀
Right (inj-l _) = Bot
Right (inj-r _) = Top

proj-l : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> (s : A ⊎ B) -> Left s -> A
proj-l (inj-l a) _ = a
proj-l (inj-r _) ()

proj-r : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> (s : A ⊎ B) -> Right s -> B
proj-r (inj-r b) _ = b
proj-r (inj-l _) ()

inj-l!=inj-r : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {a : A} {b : B}
               -> ¬(Path (A ⊎ B) (inj-l a) (inj-r b))
inj-l!=inj-r p = transport (\i -> Left (p i)) tt
