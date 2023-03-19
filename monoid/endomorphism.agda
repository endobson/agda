{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.endomorphism where

open import monoid
open import hlevel
open import base

Monoid-Endo : {ℓ₁ : Level} {A : Type ℓ₁} -> isSet A -> Monoid (A -> A)
Monoid-Endo isSet-A = record
  { ε = \x -> x
  ; _∙_ = \f g x -> f (g x)
  ; ∙-assoc = refl
  ; ∙-left-ε = refl
  ; ∙-right-ε = refl
  ; isSet-Domain = isSetΠ (\_ -> isSet-A)
  }
