{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.exponentiation where

open import additive-group
open import base
open import nat.even-odd
open import order
open import ordered-semiring
open import semiring.exponentiation
open import ordered-semiring.squares
open import relation
open import semiring

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{COS : CompatibleOrderStr LO PO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}} where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = PO
      IS = S

  ^ℕ-even-0≤ : (x : D) (n : Nat) -> Even n -> 0# ≤ (x ^ℕ n)
  ^ℕ-even-0≤ x zero          _ = convert-≮ 1≮0
  ^ℕ-even-0≤ x (suc (suc n)) e =
    trans-≤-= (*-preserves-0≤ (convert-≮ square-≮0) (^ℕ-even-0≤ x n e)) *-assoc
