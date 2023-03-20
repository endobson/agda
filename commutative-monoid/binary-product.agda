{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid.binary-product where

open import base
open import equality
open import hlevel.sigma
open import monoid.binary-product
open import commutative-monoid

CommMonoidStr-× : {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} ->
              CommMonoid D₁ -> CommMonoid D₂ -> CommMonoid (D₁ × D₂)
CommMonoidStr-× M₁ M₂ = record
  { monoid = MonoidStr-× M₁.monoid M₂.monoid
  ; ∙-commute = cong2 _,_ M₁.∙-commute M₂.∙-commute
  }
  where
  module M₁ = CommMonoid M₁
  module M₂ = CommMonoid M₂

CommMonoidʰ-proj₁ : {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} ->
                    (CM₁ : CommMonoid D₁) (CM₂ : CommMonoid D₂) ->
                    CommMonoidʰᵉ (CommMonoidStr-× CM₁ CM₂) CM₁ proj₁
CommMonoidʰ-proj₁ _ _ .CommMonoidʰ.preserves-ε = refl
CommMonoidʰ-proj₁ _ _ .CommMonoidʰ.preserves-∙ x y = refl

CommMonoidʰ-proj₂ : {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} ->
                    (CM₁ : CommMonoid D₁) (CM₂ : CommMonoid D₂) ->
                    CommMonoidʰᵉ (CommMonoidStr-× CM₁ CM₂) CM₂ proj₂
CommMonoidʰ-proj₂ _ _ .CommMonoidʰ.preserves-ε = refl
CommMonoidʰ-proj₂ _ _ .CommMonoidʰ.preserves-∙ x y = refl


CommMonoid-× : {ℓ₁ ℓ₂ : Level} -> CommMonoidT ℓ₁ -> CommMonoidT ℓ₂ -> CommMonoidT (ℓ-max ℓ₁ ℓ₂)
CommMonoid-× (D₁ , M₁) (D₂ , M₂) = (D₁ × D₂) , CommMonoidStr-× M₁ M₂
