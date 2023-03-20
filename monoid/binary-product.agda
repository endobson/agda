{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.binary-product where

open import base
open import hlevel.sigma
open import equality
open import monoid

MonoidStr-× : {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} ->
              Monoid D₁ -> Monoid D₂ -> Monoid (D₁ × D₂)
MonoidStr-× M₁ M₂ = record
  { ε = M₁.ε , M₂.ε
  ; _∙_ = \(x1 , x2) (y1 , y2) -> (x1 M₁.∙ y1) , (x2 M₂.∙ y2)
  ; ∙-assoc = cong2 _,_ M₁.∙-assoc M₂.∙-assoc
  ; ∙-left-ε = cong2 _,_ M₁.∙-left-ε M₂.∙-left-ε
  ; ∙-right-ε = cong2 _,_ M₁.∙-right-ε M₂.∙-right-ε
  ; isSet-Domain = isSet× M₁.isSet-Domain M₂.isSet-Domain
  }
  where
  module M₁ = Monoid M₁
  module M₂ = Monoid M₂

Monoid-× : {ℓ₁ ℓ₂ : Level} -> MonoidT ℓ₁ -> MonoidT ℓ₂ -> MonoidT (ℓ-max ℓ₁ ℓ₂)
Monoid-× (D₁ , M₁) (D₂ , M₂) = (D₁ × D₂) , MonoidStr-× M₁ M₂
