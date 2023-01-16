{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.nat where

open import base
open import equality
open import nat.arithmetic
open import nat.order.base
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.decidable
open import semiring
open import semiring.instances.nat

private
  +-left-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (x +' m) ≤ (x +' n)
  +-left-≤⁺ zero    lt = lt
  +-left-≤⁺ (suc x) lt = suc-≤ (+-left-≤⁺ x lt)

  *-left-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (x *' m) ≤ (x *' n)
  *-left-≤⁺         zero    lt = zero-≤
  *-left-≤⁺ {m} {n} (suc x) lt = trans-≤ lt2 (+-left-≤⁺ n (*-left-≤⁺ x lt))
    where
    lt2 : (m +' x *' m) ≤ (n +' x *' m)
    lt2 = (subst2 _≤_ (+'-commute {x *' m}) (+'-commute {x *' m}) (+-left-≤⁺ (x *' m) lt))

  +-left-<⁺ : {m n : Nat} -> (x : Nat) -> m < n -> (x +' m) < (x +' n)
  +-left-<⁺ zero    lt = lt
  +-left-<⁺ (suc x) lt = suc-≤ (+-left-<⁺ x lt)

  *-left-<⁺ : {x m n : Nat} -> x > 0 -> m < n -> (x *' m) < (x *' n)
  *-left-<⁺ {zero}             x-gt lt = bot-elim (zero-≮ x-gt)
  *-left-<⁺ {suc x} {m} {n} x-gt lt =
    trans-<-≤ lt2 (+-left-≤⁺ n (*-left-≤⁺ x (weaken-< lt)))
    where
    lt2 : (m +' x *' m) < (n +' x *' m)
    lt2 = (subst2 _<_ (+'-commute {x *' m}) (+'-commute {x *' m}) (+-left-<⁺ (x *' m) lt))

abstract
  instance
    LinearlyOrderedSemiringStr-ℕ : LinearlyOrderedSemiringStr NatSemiring LinearOrderStr-ℕ
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.+₁-preserves-< =
      +-left-<⁺ _
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.*₁-preserves-< =
      *-left-<⁺
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.*₁-flips-< a<0 =
      bot-elim (zero-≮ a<0)

    StronglyLinearlyOrderedSemiringStr-ℕ : StronglyLinearlyOrderedSemiringStr NatSemiring LinearOrderStr-ℕ
    StronglyLinearlyOrderedSemiringStr-ℕ = StronglyLinearlyOrderedSemiringStr-Dec<

    PartiallyOrderedSemiringStr-ℕ : PartiallyOrderedSemiringStr NatSemiring PartialOrderStr-ℕ
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.+₁-preserves-≤ =
      +-left-≤⁺ _
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.*₁-preserves-≤ {a} 0≤a =
      *-left-≤⁺ a
