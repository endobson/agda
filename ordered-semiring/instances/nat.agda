{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.nat where

open import base
open import equality
open import nat.arithmetic
open import nat.order.base
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import ordered-semiring
open import ordered-semiring.decidable
open import semiring
open import semiring.instances.nat

private
  *-left-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (x *' m) ≤ (x *' n)
  *-left-≤⁺         zero    lt = zero-≤
  *-left-≤⁺ {m} {n} (suc x) lt = trans-≤ lt2 (+₁-preserves-≤ (*-left-≤⁺ x lt))
    where
    lt2 : (m +' x *' m) ≤ (n +' x *' m)
    lt2 = (subst2 _≤_ (+'-commute {x *' m}) (+'-commute {x *' m}) (+₁-preserves-≤ lt))

  *-left-<⁺ : {x m n : Nat} -> x > 0 -> m < n -> (x *' m) < (x *' n)
  *-left-<⁺ {zero}             x-gt lt = bot-elim (zero-≮ x-gt)
  *-left-<⁺ {suc x} {m} {n} x-gt lt =
    trans-<-≤ lt2 (+₁-preserves-≤ (*-left-≤⁺ x (weaken-< lt)))
    where
    lt2 : (m +' x *' m) < (n +' x *' m)
    lt2 = (subst2 _<_ (+'-commute {x *' m}) (+'-commute {x *' m}) (+₁-preserves-< lt))

abstract
  instance
    LinearlyOrderedSemiringStr-ℕ : LinearlyOrderedSemiringStr NatSemiring useⁱ
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.*₁-preserves-< =
      *-left-<⁺
    LinearlyOrderedSemiringStr-ℕ .LinearlyOrderedSemiringStr.*₁-flips-< a<0 =
      bot-elim (zero-≮ a<0)

    StronglyLinearlyOrderedSemiringStr-ℕ : StronglyLinearlyOrderedSemiringStr NatSemiring useⁱ
    StronglyLinearlyOrderedSemiringStr-ℕ = StronglyLinearlyOrderedSemiringStr-Dec<

    NonTrivalLinearlyOrderedSemiringStr-ℕ :
      NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℕ
    NonTrivalLinearlyOrderedSemiringStr-ℕ = record { 0<1 = refl-≤ }

    PartiallyOrderedSemiringStr-ℕ : PartiallyOrderedSemiringStr NatSemiring useⁱ
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.0≤1 = weaken-< 0<1
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.*₁-preserves-≤ {a} 0≤a =
      *-left-≤⁺ a
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.*₁-flips-≤ {zero} a≤0 _ =
      refl-≤
    PartiallyOrderedSemiringStr-ℕ .PartiallyOrderedSemiringStr.*₁-flips-≤ {suc a} a≤0 _ =
      bot-elim (zero-≮ a≤0)

    StronglyPartiallyOrderedSemiringStr-ℕ :
      StronglyPartiallyOrderedSemiringStr NatSemiring useⁱ useⁱ
    StronglyPartiallyOrderedSemiringStr-ℕ = StronglyPartiallyOrderedSemiringStr-Dec<
