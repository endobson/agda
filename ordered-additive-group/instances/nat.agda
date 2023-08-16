{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.nat where

open import additive-group.instances.nat
open import base
open import equality
open import nat.arithmetic
open import nat.order.base
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.decidable

private
  +-left-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (x +' m) ≤ (x +' n)
  +-left-≤⁺ zero    lt = lt
  +-left-≤⁺ (suc x) lt = suc-≤ (+-left-≤⁺ x lt)

  +-left-<⁺ : {m n : Nat} -> (x : Nat) -> m < n -> (x +' m) < (x +' n)
  +-left-<⁺ zero    lt = lt
  +-left-<⁺ (suc x) lt = suc-≤ (+-left-<⁺ x lt)

abstract
  instance
    LinearlyOrderedAdditiveStr-ℕ : LinearlyOrderedAdditiveStr useⁱ useⁱ
    LinearlyOrderedAdditiveStr-ℕ =
      LinearlyOrderedAdditiveStr-Dec< (+-left-<⁺ _)

    PartiallyOrderedAdditiveStr-ℕ : PartiallyOrderedAdditiveStr useⁱ useⁱ
    PartiallyOrderedAdditiveStr-ℕ .PartiallyOrderedAdditiveStr.+₁-preserves-≤ =
      +-left-≤⁺ _

    StronglyPartiallyOrderedAdditiveStr-ℕ :
      StronglyPartiallyOrderedAdditiveStr useⁱ useⁱ
    StronglyPartiallyOrderedAdditiveStr-ℕ = StronglyPartiallyOrderedAdditiveStr-Dec<
