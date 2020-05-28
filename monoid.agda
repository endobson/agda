{-# OPTIONS --cubical --safe --exact-split #-}

module monoid where

open import base
open import equality
open import functions

record Monoid {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  infixl 6 _∙_

  field
    ε : Domain
    _∙_ : Domain -> Domain -> Domain
    ∙-assoc : {m n o : Domain} -> (m ∙ n) ∙ o == m ∙ (n ∙ o)
    ∙-left-ε : {m : Domain} -> (ε ∙ m) == m
    ∙-right-ε : {m : Domain} -> (m ∙ ε) == m
  
  ∙-right : {m n o : Domain} -> (n == o) -> m ∙ n == m ∙ o
  ∙-right {m} p i = m ∙ p i
  
  ∙-left : {m n o : Domain} -> (n == o) -> n ∙ m == o ∙ m
  ∙-left {m} p i = p i ∙ m


record Monoidʰ
    {ℓ₁ ℓ₂ : Level} 
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{M₁ : Monoid D₁}} {{M₂ : Monoid D₂}}
    (f : D₁ -> D₂)
    : Type (ℓ-max ℓ₁ ℓ₂) where
  module M₁ = Monoid M₁
  module M₂ = Monoid M₂

  field
    preserves-ε : f M₁.ε == M₂.ε
    preserves-∙ : ∀ x y -> f (x M₁.∙ y) == (f x) M₂.∙ (f y)


_∘ʰ_ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃} 
  {M₁ : Monoid D₁} {M₂ : Monoid D₂} {M₃ : Monoid D₃}
  {f : D₂ -> D₃} {g : D₁ -> D₂} 
  -> (Monoidʰ {{M₂}} {{M₃}} f) -> (Monoidʰ {{M₁}} {{M₂}} g)
  -> (Monoidʰ {{M₁}} {{M₃}} (f ∘ g))
_∘ʰ_ {M₁ = M₁} {M₃ = M₃} {f = f} {g = g} f' g' = res
  where
  module M₁ = Monoid M₁
  module M₃ = Monoid M₃
  module f' = Monoidʰ {{_}} {{_}} f'
  module g' = Monoidʰ {{_}} {{_}} g'

  preserves-ε : (f ∘ g) M₁.ε == M₃.ε
  preserves-ε = (cong f g'.preserves-ε) >=> f'.preserves-ε

  preserves-∙ : ∀ x y -> (f ∘ g) (x M₁.∙ y) == ((f ∘ g) x) M₃.∙ ((f ∘ g) y)
  preserves-∙ x y = (cong f (g'.preserves-∙ x y)) >=> f'.preserves-∙ (g x) (g y)

  res : (Monoidʰ {{M₁}} {{M₃}} (f ∘ g))
  res = record {
    preserves-ε = preserves-ε ;
    preserves-∙ = preserves-∙
    }
