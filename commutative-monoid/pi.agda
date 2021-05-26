{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid.pi where

open import base
open import equality
open import monoid
open import monoid.pi
open import funext
open import commutative-monoid

CommMonoidStr-Π : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {D : A -> Type ℓ₂} ->
                  ((a : A) -> CommMonoid (D a)) -> CommMonoid ((a : A) -> (D a))
CommMonoidStr-Π M = record
  { monoid = MonoidStr-Π (\a -> CommMonoid.monoid (M a))
  ; ∙-commute = funExt (\a -> (CommMonoid.∙-commute (M a)))
  }

CommMonoid-Π : {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) -> (A -> CommMonoidT ℓ₂) -> CommMonoidT (ℓ-max ℓ₁ ℓ₂)
CommMonoid-Π A M = ((a : A) -> (fst (M a))) , CommMonoidStr-Π (\a -> (snd (M a)))