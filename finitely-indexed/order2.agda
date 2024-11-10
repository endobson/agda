{-# OPTIONS --cubical --safe --exact-split #-}

module finitely-indexed.order2 where

open import base
open import equality
open import equivalence
open import fin-algebra
open import functions
open import finitely-indexed
open import finset
open import finset.order
open import finset.instances
open import finset.choice
open import finset.order.base
open import hlevel
open import nat.order using (WellFounded-Nat<)
open import order
open import order.instances.nat
open import relation
open import truncation
open import maybe

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C : Type ℓ

private
  isUpperBound : Type ℓ -> Nat -> Type ℓ
  isUpperBound A n = ∥ FinT n ↠ A ∥

  isLowerBound : Type ℓ -> Nat -> Type ℓ
  isLowerBound A n = ∥ FinT n ↪ A ∥


  combine : (n m : Nat) -> (FinT n ↠ A) -> (FinT m ↪ A) -> m ≤ n
  combine {A = A} n m (f , sur-f) (g , emb-g) =
    unsquash isProp-≤ (∥-map handle search-res)
    where
    search-res : ∃[ h ∈ (FinT m -> FinT n) ] (∀ j -> f (h j) == g j)
    search-res = finite-choice (FinSet-FinT m) (\j -> sur-f (g j))

    handle : Σ[ h ∈ (FinT m -> FinT n) ] (∀ j -> f (h j) == g j) ->
              m ≤ n
    handle (h , p) = isInjective->FinSet≤ (FinSet-FinT m) (FinSet-FinT n) h inj-h
      where
      inj-h : isInjective h
      inj-h {a1 = a1} {a2 = a2} ha1=ha2 =
        isEqInv (emb-g a1 a2) (sym (p a1) >=> cong f ha1=ha2 >=> p a2)



--private
--  Size<⁺ : (A : Type ℓ₁) (B : Type ℓ₂) (ℓ : Level) -> Type _
--  Size<⁺ A B ℓ = ∃[ C ∈ Type ℓ ] (C ↠ A × (Maybe C ↪ B))
--
--  reverse-surjection : (A ↠ B) -> (B ↪ A)
--  reverse-surjection {A = A} {B = B} (f , sur-f) = ?
--    where
--    check-sur-f : ∀ (b : B) -> ∃[ a ∈ A ] (f a == b)
--    check-sur-f = sur-f
