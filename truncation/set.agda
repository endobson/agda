{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.set where

open import base
open import equality-path
open import hlevel.base
open import hlevel.pi
open import relation

private
  variable
    ℓ : Level
    A B C : Type ℓ


data Squash₀ {ℓ : Level} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A -> Squash₀ A
  squash : isSet (Squash₀ A)

unsquash₀ : isSet A -> Squash₀ A -> A
unsquash₀ h ∣ a ∣ = a
unsquash₀ h (squash a₁ a₂ p₁ p₂ i j) =
  h (unsquash₀ h a₁) (unsquash₀ h a₂)
    (\i -> unsquash₀ h (p₁ i))
    (\i -> unsquash₀ h (p₂ i))
    i j

∥₀-map : (A -> B) -> Squash₀ A -> Squash₀ B
∥₀-map f ∣ a ∣ = ∣ f a ∣
∥₀-map f (squash a₁ a₂ p₁ p₂ i j) =
  let f' = ∥₀-map f in
    squash (f' a₁) (f' a₂) (cong f' p₁) (cong f' p₂) i j

∥₀-map2 : (A -> B -> C) -> Squash₀ A -> Squash₀ B -> Squash₀ C
∥₀-map2 f ∣ a ∣ = ∥₀-map (f a)
∥₀-map2 f (squash a₁ a₂ p₁ p₂ i j) b =
  let f' = ∥₀-map2 f in
    squash (f' a₁ b) (f' a₂ b) (\i -> f' (p₁ i) b) (\i -> f' (p₂ i) b) i j

module _ {P : Pred (Squash₀ A) ℓ} where
  ∥₀-elim : (∀ (s : Squash₀ A) -> isSet (P s)) ->
            ((a : A) -> P ∣ a ∣) ->
            (s : Squash₀ A) -> P s
  ∥₀-elim h f ∣ a ∣ = f a
  ∥₀-elim h f (squash s₁ s₂ p₁ p₂ i j) =
    isOfHLevel->isOfHLevelDep 2 h
      (f' s₁) (f' s₂) (cong f' p₁) (cong f' p₂)
      (squash s₁ s₂ p₁ p₂) i j
    where
    f' : (s : Squash₀ A) -> P s
    f' = ∥₀-elim h f

module _ {P : Pred (Squash₀ A) ℓ} where
  ∥₀-elim' : (∀ (a : A) -> isSet (P ∣ a ∣)) ->
             ((a : A) -> P ∣ a ∣) ->
             (s : Squash₀ A) -> P s
  ∥₀-elim' h f =
    ∥₀-elim
      (∥₀-elim (\_ -> isProp->isSet isProp-isSet) h)
      f


module _ {P : Rel (Squash₀ A) ℓ} where
  ∥₀-elim2' : (∀ (a₁ a₂ : A) -> isSet (P ∣ a₁ ∣ ∣ a₂ ∣)) ->
              ((a₁ a₂ : A) -> P ∣ a₁ ∣ ∣ a₂ ∣) ->
              (s₁ s₂ : Squash₀ A) -> P s₁ s₂
  ∥₀-elim2' h f =
    ∥₀-elim'
      (\a₁ -> isSetΠ (∥₀-elim' (\_ -> isProp->isSet isProp-isSet) (h a₁)))
      (\a₁ -> ∥₀-elim' (h a₁) (f a₁))

module _ {P : Squash₀ A -> Squash₀ A -> Squash₀ A -> Type ℓ} where
  ∥₀-elim3' : (∀ (a₁ a₂ a₃ : A) -> isSet (P (∣ a₁ ∣) (∣ a₂ ∣) (∣ a₃ ∣))) ->
              ((a₁ a₂ a₃ : A) -> P (∣ a₁ ∣) (∣ a₂ ∣) (∣ a₃ ∣)) ->
              (s₁ s₂ s₃ : Squash₀ A) -> P s₁ s₂ s₃
  ∥₀-elim3' h f =
    ∥₀-elim'
      (\a₁ -> isSetΠ2 (∥₀-elim2' (\_ _ -> isProp->isSet isProp-isSet) (h a₁)))
      (\a₁ -> ∥₀-elim2' (h a₁) (f a₁))
