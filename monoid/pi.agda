{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.pi where

open import base
open import equality
open import monoid
open import funext

MonoidStr-Π : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {D : A -> Type ℓ₂} ->
              ((a : A) -> Monoid (D a)) -> Monoid ((a : A) -> (D a))
MonoidStr-Π M = record
  { ε = (\a -> (Monoid.ε (M a)))
  ; _∙_ =  (\f g a -> (Monoid._∙_ (M a)) (f a) (g a))
  ; ∙-assoc = funExt (\a -> (Monoid.∙-assoc (M a)))
  ; ∙-left-ε = funExt (\a -> (Monoid.∙-left-ε (M a)))
  ; ∙-right-ε = funExt (\a -> (Monoid.∙-right-ε (M a)))
  }

Monoid-Π : {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) -> (A -> MonoidT ℓ₂) -> MonoidT (ℓ-max ℓ₁ ℓ₂)
Monoid-Π A M = ((a : A) -> (fst (M a))) , MonoidStr-Π (\a -> (snd (M a)))
