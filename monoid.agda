{-# OPTIONS --cubical --safe --exact-split #-}

module monoid where

open import base

record Monoid {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  infixl 6 _∙_

  field
    ε : Domain
    _∙_ : Domain -> Domain -> Domain
    ∙-assoc : {m n o : Domain} -> (m ∙ n) ∙ o == m ∙ (n ∙ o)
    ∙-left-ε : {m : Domain} -> (ε ∙ m) == m
    ∙-right-ε : {m : Domain} -> (m ∙ ε) == m


record MonoidHomomorphism {ℓ : Level} {D₁ D₂ : Type ℓ} (M₁ : Monoid D₁) (M₂ : Monoid D₂)
                          (f : D₁ -> D₂) : Type ℓ where
  module M₁ = Monoid M₁
  module M₂ = Monoid M₂

  field
    preserves-ε : f M₁.ε == M₂.ε
    preserves-∙ : ∀ x y -> f (x M₁.∙ y) == (f x) M₂.∙ (f y)
