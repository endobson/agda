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


record MonoidHomomorphism
    {ℓ₁ ℓ₂ : Level} 
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    (M₁ : Monoid D₁) (M₂ : Monoid D₂)
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
  -> (MonoidHomomorphism M₂ M₃ f) -> (MonoidHomomorphism M₁ M₂ g)
  -> (MonoidHomomorphism M₁ M₃ (f ∘ g))
_∘ʰ_ {M₁ = M₁} {M₃ = M₃} {f = f} {g = g} f' g' = res
  where
  module M₁ = Monoid M₁
  module M₃ = Monoid M₃
  module f' = MonoidHomomorphism f'
  module g' = MonoidHomomorphism g'

  preserves-ε : (f ∘ g) M₁.ε == M₃.ε
  preserves-ε = (cong f g'.preserves-ε) >=> f'.preserves-ε

  preserves-∙ : ∀ x y -> (f ∘ g) (x M₁.∙ y) == ((f ∘ g) x) M₃.∙ ((f ∘ g) y)
  preserves-∙ x y = (cong f (g'.preserves-∙ x y)) >=> f'.preserves-∙ (g x) (g y)

  res : (MonoidHomomorphism M₁ M₃ (f ∘ g))
  res = record {
    preserves-ε = preserves-ε ;
    preserves-∙ = preserves-∙
    }
