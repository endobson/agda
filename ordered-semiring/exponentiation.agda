{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.exponentiation where

open import additive-group
open import base
open import equivalence
open import nat.even-odd
open import order
open import ordered-semiring
open import ordered-semiring.negated
open import ordered-semiring.squares
open import relation
open import semiring
open import semiring.exponentiation
open import sum

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
  ^ℕ-even-0≤ x zero          _ = 0≤1
  ^ℕ-even-0≤ x (suc (suc n)) e =
    trans-≤-= (*-preserves-0≤ (convert-≮ square-≮0) (^ℕ-even-0≤ x n e)) *-assoc

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}} where
  private
    instance
      IACM = ACM
      ILO = LO
      IS = S

  ^ℕ-preserves-<>0 : {x : D} -> x <> 0# -> (n : Nat) -> (x ^ℕ n) <> 0#
  ^ℕ-preserves-<>0 x<>0 (suc n) =
    eqFun *-<>0-equiv (x<>0 , ^ℕ-preserves-<>0 x<>0 n)
  ^ℕ-preserves-<>0 (inj-l x<0) zero = inj-r (non-trivial-0<1 x<0)
  ^ℕ-preserves-<>0 (inj-r 0<x) zero = inj-r (non-trivial-0<1 0<x)

  module _ where
    private
      instance
        PO = isLinearOrder->isPartialOrder-≯ LO
        CPO = CompatibleNegatedLinearOrder LO
        POS = PartiallyOrderedSemiringStr-Negated S LO

    ^ℕ-even-0< : {x : D} -> x <> 0# -> (n : Nat) -> Even n -> 0# < (x ^ℕ n)
    ^ℕ-even-0< x<>0 n en =
      proj-¬l (^ℕ-preserves-<>0 x<>0 n) (convert-≤ (^ℕ-even-0≤ _ n en))

  ^ℕ-odd-0< : {x : D} -> 0# < x -> (n : Nat) -> Odd n -> 0# < (x ^ℕ n)
  ^ℕ-odd-0< 0<x (suc n) on = *-preserves-0< 0<x (^ℕ-even-0< (inj-r 0<x) n on)

  ^ℕ-odd-<0 : {x : D} -> x < 0# -> (n : Nat) -> Odd n -> (x ^ℕ n) < 0#
  ^ℕ-odd-<0 x<0 (suc n) on = *₂-preserves-<0 x<0 (^ℕ-even-0< (inj-l x<0) n on)
