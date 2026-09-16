{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.functions where

open import additive-group
open import base


module _ {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
         {{ACM : AdditiveCommMonoid D₁}}
         {{AG : AdditiveGroup ACM}}
  where

  isEvenFunction : (f : D₁ -> D₂) -> Type (ℓ-max ℓ₁ ℓ₂)
  isEvenFunction f = ∀ x -> f (- x) == f x


module _ {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
         {{ACM₁ : AdditiveCommMonoid D₁}}
         {{ACM₂ : AdditiveCommMonoid D₂}}
         {{AG₁ : AdditiveGroup ACM₁}}
         {{AG₂ : AdditiveGroup ACM₂}}
  where

  isOddFunction : (f : D₁ -> D₂) -> Type (ℓ-max ℓ₁ ℓ₂)
  isOddFunction f = ∀ x -> f (- x) == - (f x)
