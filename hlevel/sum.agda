{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.sum where

open import base
open import equality-path
open import hlevel.base
open import sum

private
  variable
    ℓ : Level
    A₁ A₂ : Type ℓ

opaque
  isProp⊎ : isProp A₁ -> isProp A₂ -> (A₁ -> ¬ A₂) -> isProp (A₁ ⊎ A₂)
  isProp⊎ ha hb neg (inj-l a1) (inj-l a2) = cong inj-l (ha a1 a2)
  isProp⊎ ha hb neg (inj-l a1) (inj-r b2) = bot-elim (neg a1 b2)
  isProp⊎ ha hb neg (inj-r b1) (inj-l a2) = bot-elim (neg a2 b1)
  isProp⊎ ha hb neg (inj-r b1) (inj-r b2) = cong inj-r (hb b1 b2)


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         (isSet-A : isSet A) (isSet-B : isSet B) where

  private
    isProp-⊎Cover : (s₁ s₂ : A ⊎ B) -> isProp (⊎Cover s₁ s₂)
    isProp-⊎Cover (inj-l a₁) (inj-l a₂) (lift p₁) (lift p₂) =
      cong lift (isSet-A a₁ a₂ p₁ p₂)
    isProp-⊎Cover (inj-l a₁) (inj-r b₂) (lift ())
    isProp-⊎Cover (inj-r b₁) (inj-l a₂) (lift ())
    isProp-⊎Cover (inj-r b₁) (inj-r b₂) (lift p₁) (lift p₂) =
      cong lift (isSet-B b₁ b₂ p₁ p₂)

  opaque
    isSet-⊎ : isSet (A ⊎ B)
    isSet-⊎ s₁ s₂ = subst isProp (⊎-cover==path s₁ s₂) (isProp-⊎Cover s₁ s₂)
