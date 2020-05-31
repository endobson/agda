{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid where

open import base
open import equality
open import functions
import monoid

record CommMonoid {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    {{monoid}} : monoid.Monoid Domain
  open monoid.Monoid monoid public

  field
    ∙-commute : {m n : Domain} -> (m ∙ n) == (n ∙ m)


record CommMonoidʰ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{M₁ : CommMonoid D₁}} {{M₂ : CommMonoid D₂}}
    (f : D₁ -> D₂)
    : Type (ℓ-max ℓ₁ ℓ₂) where
  module M₁ = CommMonoid M₁
  module M₂ = CommMonoid M₂

  field
    preserves-ε : f M₁.ε == M₂.ε
    preserves-∙ : ∀ x y -> f (x M₁.∙ y) == (f x) M₂.∙ (f y)

_∘ʰ_ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃}
  {M₁ : CommMonoid D₁} {M₂ : CommMonoid D₂} {M₃ : CommMonoid D₃}
  {f : D₂ -> D₃} {g : D₁ -> D₂}
  -> (CommMonoidʰ {{M₂}} {{M₃}} f)
  -> (CommMonoidʰ {{M₁}} {{M₂}} g)
  -> (CommMonoidʰ {{M₁}} {{M₃}} (f ∘ g))
_∘ʰ_ {M₁ = M₁} {M₃ = M₃} {f = f} {g = g} f' g' = res
  where
  module M₁ = CommMonoid M₁
  module M₃ = CommMonoid M₃
  module f' = CommMonoidʰ {{_}} {{_}} f'
  module g' = CommMonoidʰ {{_}} {{_}} g'

  preserves-ε : (f ∘ g) M₁.ε == M₃.ε
  preserves-ε = (cong f g'.preserves-ε) >=> f'.preserves-ε

  preserves-∙ : ∀ x y -> (f ∘ g) (x M₁.∙ y) == ((f ∘ g) x) M₃.∙ ((f ∘ g) y)
  preserves-∙ x y = (cong f (g'.preserves-∙ x y)) >=> f'.preserves-∙ (g x) (g y)

  res : (CommMonoidʰ {{M₁}} {{M₃}} (f ∘ g))
  res = record {
    preserves-ε = preserves-ε ;
    preserves-∙ = preserves-∙
    }
