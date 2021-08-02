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


app-to : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A -> Type ℓ₂} -> (a : A) -> ((a : A) -> B a) -> B a
app-to a f = f a

app-toʰ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A -> Type ℓ₂} (CM-B : (a : A) -> CommMonoid (B a)) ->
          (a : A) -> (CommMonoidʰᵉ (CommMonoidStr-Π CM-B) (CM-B a) (app-to a))
app-toʰ CM-B a = record
  { preserves-ε = refl
  ; preserves-∙ = \_ _ -> refl
  }
