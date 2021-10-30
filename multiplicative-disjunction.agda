{-# OPTIONS --cubical --safe --exact-split #-}

module multiplicative-disjunction where

open import base
open import hlevel

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

infixr 1 _⅋_

record _⅋_ (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor ⅋-cons
  field
    left : ¬ B -> A
    right : ¬ A -> B

isProp-⅋ : isProp A -> isProp B -> isProp (A ⅋ B)
isProp-⅋ hA hB (⅋-cons l1 r1)  (⅋-cons l2 r2) i =
  ⅋-cons (isPropΠ (\_ -> hA) l1 l2 i) (isPropΠ (\_ -> hB) r1 r2 i)

⅋-left : A ⅋ B -> ¬ B -> A
⅋-left ab = _⅋_.left ab
⅋-right : A ⅋ B -> ¬ A -> B
⅋-right ab = _⅋_.right ab
