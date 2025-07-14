{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.truncation where

open import base
open import isomorphism
open import cubical
open import equivalence
open import functions
open import equality-path
open import hlevel.base
open import hlevel.htype
open import pointed.base
open import pointed.loop-space
open import truncation
open import truncation.set

Squash₀∙ : {ℓ : Level} -> Type∙ ℓ -> Type∙ ℓ
Squash₀∙ (A , ★A) = Squash₀ A , ∣ ★A  ∣

Squash∙ : {ℓ : Level} -> Type∙ ℓ -> Type∙ ℓ
Squash∙ (A , ★A) = Squash A , ∣ ★A  ∣

module _ {ℓ : Level} (A : Type ℓ) (a₁ a₂ : A) where
  Squash-path-eq : Squash (a₁ == a₂) ≃ Path (Squash₀ A) (∣ a₁ ∣) (∣ a₂ ∣)
  Squash-path-eq = isoToEquiv (isProp->iso for encode squash (squash _ _))
    where
    for : Squash (a₁ == a₂) -> Path (Squash₀ A) (∣ a₁ ∣) (∣ a₂ ∣)
    for = ∥-elim (\_ -> squash _ _) (\p i -> ∣ p i ∣ )

    Encode : (Squash₀ A) -> (Squash₀ A) ->
             Σ (Type ℓ) isProp
    Encode =
      ∥₀-elim2'
        (\_ _ -> isSet-hProp)
        (\a b -> ∥ a == b ∥ , squash)

    encode-refl : ∀ (s : Squash₀ A) -> ⟨ Encode s s ⟩
    encode-refl =
      ∥₀-elim
        (\s -> isProp->isSet (snd (Encode s s)))
        (\a -> ∣ refl ∣)

    encode : ∀ {s₁ s₂} -> s₁ == s₂ -> ⟨ Encode s₁ s₂ ⟩
    encode {s₁} = J (\s₂ p -> ⟨ Encode s₁ s₂ ⟩) (encode-refl s₁)


module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  Squash-Ω-eq∙ : Squash∙ (Ω A∙) ≃∙ Ω (Squash₀∙ A∙)
  Squash-Ω-eq∙ = Squash-path-eq _ _ _ , refl
