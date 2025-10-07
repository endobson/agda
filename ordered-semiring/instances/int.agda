{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.int where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int
open import nat.arithmetic
open import order
open import order.instances.int
open import ordered-additive-group.instances.int
open import ordered-semiring
open import ordered-semiring.decidable
open import ordered-semiring.ring
open import ring.implementations.int
open import semiring
open import semiring.instances.nat

private
  ℤ*₁-preserves-< : {a b c : ℤ} -> 0# < a -> (b < c) -> (a * b) < (a * c)
  ℤ*₁-preserves-< {a} {b} {c} (d₁ , p₁) (d₂ , p₂) =
    d₁ *⁺ d₂ ,
    +-left (ℕ->ℤ-* >=> *-left (sym +-right-zero >=> p₁)) >=>
    sym *-distrib-+-left >=>
    *-right p₂

  ℤ*₁-preserves-≤ : {a b c : ℤ} -> 0# ≤ a -> (b ≤ c) -> (a * b) ≤ (a * c)
  ℤ*₁-preserves-≤ {a} {b} {c} (d₁ , p₁) (d₂ , p₂) =
    d₁ * d₂ ,
    +-left (ℕ->ℤ-* >=> *-left (sym +-right-zero >=> p₁)) >=>
    sym *-distrib-+-left >=>
    *-right p₂

instance
  opaque
    LinearlyOrderedSemiringStr-ℤ : LinearlyOrderedSemiringStr IntSemiring useⁱ
    LinearlyOrderedSemiringStr-ℤ = LinearlyOrderedSemiringStr-Ring
      ℤ*₁-preserves-<

    StronglyLinearlyOrderedSemiringStr-ℤ : StronglyLinearlyOrderedSemiringStr IntSemiring useⁱ
    StronglyLinearlyOrderedSemiringStr-ℤ = StronglyLinearlyOrderedSemiringStr-Dec<

    NonTrivalLinearlyOrderedSemiringStr-ℤ :
      NonTrivialLinearlyOrderedSemiringStr LinearlyOrderedSemiringStr-ℤ
    NonTrivalLinearlyOrderedSemiringStr-ℤ = record { 0<1 = ( 1 , tt) , +-right-zero }

    PartiallyOrderedSemiringStr-ℤ : PartiallyOrderedSemiringStr IntSemiring useⁱ
    PartiallyOrderedSemiringStr-ℤ = PartiallyOrderedSemiringStr-Ring
      (weaken-< 0<1) ℤ*₁-preserves-≤

    StronglyPartiallyOrderedSemiringStr-ℤ :
      StronglyPartiallyOrderedSemiringStr IntSemiring useⁱ useⁱ
    StronglyPartiallyOrderedSemiringStr-ℤ = StronglyPartiallyOrderedSemiringStr-Dec<
