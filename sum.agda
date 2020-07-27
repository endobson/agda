{-# OPTIONS --cubical --safe --exact-split #-}

module sum where

open import base
open import equality
open import functions
open import hlevel.base
open import isomorphism
open import relation

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C D : Type ℓ

open Iso

⊎-map : (A -> C) -> (B -> D) -> (A ⊎ B) -> (C ⊎ D)
⊎-map f g (inj-l a) = inj-l (f a)
⊎-map f g (inj-r b) = inj-r (g b)

⊎-map-left : (f : A -> C) -> (A ⊎ B) -> (C ⊎ B)
⊎-map-left f = ⊎-map f (\x -> x)

⊎-map-right : (g : B -> D) -> (A ⊎ B) -> (A ⊎ D)
⊎-map-right g = ⊎-map (\x -> x) g

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

Discrete⊎ : Discrete A -> Discrete B -> Discrete (A ⊎ B)
Discrete⊎ da db (inj-l a1) (inj-l a2) with (da a1 a2)
... | yes a-path = yes (cong inj-l a-path)
... | no ¬a-path = no (¬a-path ∘ f)
  where
  f : (inj-l a1) == (inj-l a2) -> a1 == a2
  f p i = proj-l (p i) (Left-path i)
    where
    Left-path : PathP (\i -> Left (p i)) tt tt
    Left-path i = transport-filler (\i -> Left (p i)) tt i
Discrete⊎ da db (inj-l a1) (inj-r b2) = no inj-l!=inj-r
Discrete⊎ da db (inj-r b1) (inj-l a2) = no (inj-l!=inj-r ∘ sym)
Discrete⊎ da db (inj-r b1) (inj-r b2) with (db b1 b2)
... | yes b-path = yes (cong inj-r b-path)
... | no ¬b-path = no (¬b-path ∘ f)
  where
  f : (inj-r b1) == (inj-r b2) -> b1 == b2
  f p i = proj-r (p i) (Right-path i)
    where
    Right-path : PathP (\i -> Right (p i)) tt tt
    Right-path i = transport-filler (\i -> Right (p i)) tt i
