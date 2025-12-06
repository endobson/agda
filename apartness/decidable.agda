{-# OPTIONS --cubical --safe --exact-split #-}

module apartness.decidable where

open import apartness
open import decision
open import base
open import equality-path
open import equivalence
open import isomorphism

module _ {ℓD ℓ#₁ ℓ#₂ : Level} {D : Type ℓD} {_#₁_ : Rel D ℓ#₁} {_#₂_ : Rel D ℓ#₂}
  (TA₁ : isTightApartness _#₁_)
  (TA₂ : isTightApartness _#₂_)
  (Dec₁ : Decidable2 _#₁_)
  (Dec₂ : Decidable2 _#₂_)
  where
  private
    module TA₁ = isTightApartness TA₁
    module TA₂ = isTightApartness TA₂

  opaque
    DecidableApartness-equiv : ∀ (a b : D) -> (a #₁ b) ≃ (a #₂ b)
    DecidableApartness-equiv a b = isoToEquiv (isProp->iso for back TA₁.isProp-# TA₂.isProp-#)
      where
      for : a #₁ b -> a #₂ b
      for a#b = case (Dec₂ a b) of
        \{ (yes a#b) -> a#b
         ; (no ¬a#b) -> bot-elim (irrefl-path-# (TA₂.tight-# ¬a#b) a#b)
         }
        where
        instance
          ITA : isTightApartness _#₁_
          ITA = TA₁
      back : a #₂ b -> a #₁ b
      back a#b = case (Dec₁ a b) of
        \{ (yes a#b) -> a#b
         ; (no ¬a#b) -> bot-elim (irrefl-path-# (TA₁.tight-# ¬a#b) a#b)
         }
        where
        instance
          ITA : isTightApartness _#₂_
          ITA = TA₂
