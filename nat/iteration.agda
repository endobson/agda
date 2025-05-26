{-# OPTIONS --cubical --safe --exact-split #-}

module nat.iteration where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality-path
open import functions
open import monoid
open import nat

private
  variable
    ℓ : Level
    A : Type ℓ

opaque
  iter-commute₁ : ∀ (n : ℕ) {f g : A -> A} -> f ∘ g == g ∘ f ->
                 iter n f ∘ g == g ∘ iter n f
  iter-commute₁ zero _ = refl
  iter-commute₁ (suc n) {f} {g} p =
    cong (f ∘_) (iter-commute₁ n p) >=> cong (_∘ iter n f) p

  iter-commute₂ : ∀ (n m : ℕ) {f g : A -> A} -> f ∘ g == g ∘ f ->
                   iter n f ∘ iter m g == iter m g ∘ iter n f
  iter-commute₂ n m p =  iter-commute₁ n (sym (iter-commute₁ m (sym p)))


module _ {ℓ : Level} {A : Type ℓ} {{M : Monoid A}} where
  private
    module M = Monoid M
    instance
      Mℕ = Monoid-+ ℕ

  iter-leftAction : (a : A) -> ℕ -> A
  iter-leftAction a n = iter n (a M.∙_) M.ε

  opaque
    iter-leftActionʰ : (a : A) -> Monoidʰ (iter-leftAction a)
    iter-leftActionʰ a = record
      { preserves-ε = refl
      ; preserves-∙ = preserves-∙
      }
      where
      preserves-∙ : ∀ n m -> iter-leftAction a (n + m) == iter-leftAction a n M.∙ iter-leftAction a m
      preserves-∙ zero    m = sym M.∙-left-ε
      preserves-∙ (suc n) m = cong (a M.∙_) (preserves-∙ n m) >=> sym M.∙-assoc
