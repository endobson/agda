{-# OPTIONS --cubical --safe --exact-split #-}

module decision where

open import base

private
  variable
    ℓ : Level
    A B : Type ℓ

data Dec (A : Type ℓ) : Type ℓ where
  yes :   A -> Dec A
  no  : ¬ A -> Dec A

dec-case : (A -> B) -> (¬ A -> B) -> Dec A -> B
dec-case t f (yes a) = t a
dec-case t f (no ¬a) = f ¬a

dec-map : (A -> B) -> (B -> A) -> Dec A -> Dec B
dec-map f g (yes a) = (yes (f a))
dec-map f g (no ¬a) = (no (\b -> ¬a (g b)))

dec->⊎ : Dec A -> A ⊎ ¬ A
dec->⊎ (yes a) = inj-l a
dec->⊎ (no na) = inj-r na

comp-dec : Dec A -> Dec (¬ A)
comp-dec (yes a) = no (\ na -> na a)
comp-dec (no na) = yes na

Decidable : Pred A ℓ -> Type _
Decidable P = ∀ x -> Dec (P x)

Decidable2 : REL A B ℓ -> Type _
Decidable2 _~_ = ∀ x y -> Dec (x ~ y)
