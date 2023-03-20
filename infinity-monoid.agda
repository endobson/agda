{-# OPTIONS --cubical --safe --exact-split #-}

module infinity-monoid where

open import base
open import equality
open import functions
open import hlevel.base
import monoid

record InfinityMonoid {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
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


record InfinityMonoidʰᵉ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    (M₁ : InfinityMonoid D₁) (M₂ : InfinityMonoid D₂)
    (f : D₁ -> D₂) : Type (ℓ-max ℓ₁ ℓ₂)
    where
  module M₁ = InfinityMonoid M₁
  module M₂ = InfinityMonoid M₂

  field
    preserves-ε : f M₁.ε == M₂.ε
    preserves-∙ : ∀ x y -> f (x M₁.∙ y) == (f x) M₂.∙ (f y)

InfinityMonoidʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{M₁ : InfinityMonoid D₁}} {{M₂ : InfinityMonoid D₂}}
    (f : D₁ -> D₂)
    -> Type (ℓ-max ℓ₁ ℓ₂)
InfinityMonoidʰ {{M₁ = M₁}} {{M₂ = M₂}} f = InfinityMonoidʰᵉ M₁ M₂ f

module InfinityMonoidʰ {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {M₁ : InfinityMonoid D₁} {M₂ : InfinityMonoid D₂}
    {f : D₁ -> D₂}
    (cm : InfinityMonoidʰᵉ M₁ M₂ f) where
  open InfinityMonoidʰᵉ cm public


_∘ʰ_ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃}
  {M₁ : InfinityMonoid D₁} {M₂ : InfinityMonoid D₂} {M₃ : InfinityMonoid D₃}
  {f : D₂ -> D₃} {g : D₁ -> D₂}
  -> (InfinityMonoidʰᵉ M₂ M₃ f)
  -> (InfinityMonoidʰᵉ M₁ M₂ g)
  -> (InfinityMonoidʰᵉ M₁ M₃ (f ∘ g))
_∘ʰ_ {M₁ = M₁} {M₃ = M₃} {f = f} {g = g} f' g' = res
  where
  module M₁ = InfinityMonoid M₁
  module M₃ = InfinityMonoid M₃
  module f' = InfinityMonoidʰ f'
  module g' = InfinityMonoidʰ g'

  preserves-ε : (f ∘ g) M₁.ε == M₃.ε
  preserves-ε = (cong f g'.preserves-ε) >=> f'.preserves-ε

  preserves-∙ : ∀ x y -> (f ∘ g) (x M₁.∙ y) == ((f ∘ g) x) M₃.∙ ((f ∘ g) y)
  preserves-∙ x y = (cong f (g'.preserves-∙ x y)) >=> f'.preserves-∙ (g x) (g y)

  res : (InfinityMonoidʰᵉ M₁ M₃ (f ∘ g))
  res = record {
    preserves-ε = preserves-ε ;
    preserves-∙ = preserves-∙
    }

Monoid->InfinityMonoid : {ℓ : Level} -> {D : Type ℓ} -> monoid.Monoid D -> InfinityMonoid D
Monoid->InfinityMonoid M = record
  { ε         = monoid.Monoid.ε M
  ; _∙_       = monoid.Monoid._∙_ M
  ; ∙-assoc   = monoid.Monoid.∙-assoc M
  ; ∙-left-ε  = monoid.Monoid.∙-left-ε M
  ; ∙-right-ε = monoid.Monoid.∙-right-ε M
  }
