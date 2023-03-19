{-# OPTIONS --cubical --safe --exact-split #-}

module infinity-monoid.endomorphism where

open import infinity-monoid
open import base

InfinityMonoid-Endo : {ℓ₁ : Level} {A : Type ℓ₁} -> InfinityMonoid (A -> A)
InfinityMonoid-Endo = record
  { ε = \x -> x
  ; _∙_ = \f g x -> f (g x)
  ; ∙-assoc = refl
  ; ∙-left-ε = refl
  ; ∙-right-ε = refl
  }
