{-# OPTIONS --cubical --safe --exact-split #-}

module connected.reduce where

open import additive-group
open import additive-group.instances.nat
open import base
open import connected
open import equality-path
open import hlevel.base
open import hlevel.retract
open import nat.order
open import order
open import order.instances.nat
open import truncation.generic

private
  reduce+₁-isConnectedₙ₋₂ :
    {ℓ : Level} {A : Type ℓ} {n : Nat} ->
    isConnectedₙ₋₂ (suc n) A -> isConnectedₙ₋₂ n A
  reduce+₁-isConnectedₙ₋₂ {n = 0} _ = lift tt , \_ -> refl
  reduce+₁-isConnectedₙ₋₂ {A = A} {n = suc n} c = isContr-Retract f g gf c
    where
    f : Squashₙ (suc n) A -> Squashₙ (suc (suc n)) A
    f = ∥ₙ-elim (\_ -> isContr->isOfHLevel (suc n) c) (\a -> ∣ a ∣)

    g : Squashₙ (suc (suc n)) A -> Squashₙ (suc n) A
    g = ∥ₙ-elim (\_ -> isOfHLevelSuc (suc n) (isOfHLevel-Squashₙ (suc n)))
                (\a -> ∣ a ∣)

    gf : ∀ x -> g (f x) == x
    gf = ∥ₙ-elim (\x -> isOfHLevelSuc (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)
                 (\_ -> refl)

  reduce+-isConnectedₙ₋₂ :
    {ℓ : Level} {A : Type ℓ} (k : Nat) {n : Nat} ->
    isConnectedₙ₋₂ (k + n) A -> isConnectedₙ₋₂ n A
  reduce+-isConnectedₙ₋₂ zero c = c
  reduce+-isConnectedₙ₋₂ (suc k) c =
    reduce+-isConnectedₙ₋₂ k (reduce+₁-isConnectedₙ₋₂ c)

opaque
  reduce-isConnectedₙ₋₂ :
    {ℓ : Level} {A : Type ℓ} {n₁ n₂ : Nat} ->
    (n₁ ≤ n₂) -> isConnectedₙ₋₂ n₂ A -> isConnectedₙ₋₂ n₁ A
  reduce-isConnectedₙ₋₂ {A = A} (k , p) c =
    reduce+-isConnectedₙ₋₂ k (subst (\m -> isConnectedₙ₋₂ m A) (sym p) c)

  reduce-isConnected :
    {ℓ : Level} {A : Type ℓ} {n₁ n₂ : Nat} ->
    (n₁ ≤ n₂) -> isConnectedₙ n₂ A -> isConnectedₙ n₁ A
  reduce-isConnected lt = reduce-isConnectedₙ₋₂ (suc-≤ (suc-≤ lt))
