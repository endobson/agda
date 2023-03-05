{-# OPTIONS --cubical --safe --exact-split #-}

module sequence.partial-sums where

open import additive-group
open import base
open import equality
open import fin
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum
open import functions
open import funext
open import nat
open import order
open import ordered-additive-group
open import sequence

module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}  where
  private
    Seq : Type ℓD
    Seq = Sequence D

  partial-sums : Seq -> Seq
  partial-sums s n = finiteSum (\ ((i , _) : Fin n) -> s i)

  partial-sums-cons : (x : D) (s : Seq) (n : ℕ) ->
    partial-sums (seq-cons x s) (suc n) == x + partial-sums s n
  partial-sums-cons x s zero =
   finiteMerge-Fin1 _ _ >=>
   sym +-right-zero >=>
   +-right (sym (finiteMerge-Fin0 _ _))
  partial-sums-cons x s (suc n) = finiteMerge-FinSuc _ _

  partial-sum-split : (s : Seq) (n : ℕ) -> (partial-sums s (suc n)) == s n + partial-sums s n
  partial-sum-split s zero =
    finiteMerge-Fin1 _ _ >=>
    sym +-right-zero >=>
    +-right (sym (finiteMerge-Fin0 _ _))
  partial-sum-split s (suc n) =
    finiteMerge-FinSuc _ _ >=>
    +-right (partial-sum-split (drop1 s) n) >=>
    sym +-assoc >=>
    +-left +-commute >=>
    +-assoc >=>
    +-right (sym (finiteMerge-FinSuc _ _))

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {PO : PartialOrderStr D ℓ≤}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
          where
  private
    instance
      IACM = ACM
      IPO = PO

    Seq : Type ℓD
    Seq = Sequence D

  partial-sums-0≤ :
    (s : Seq) -> ((n : ℕ) -> 0# ≤ s n) -> (n : ℕ) -> 0# ≤ partial-sums s n
  partial-sums-0≤ s 0≤s zero =
    subst2 _≤_ (finiteMerge-Fin0 _ _) refl refl-≤
  partial-sums-0≤ s 0≤s (suc n) =
    subst (0# ≤_) (sym (partial-sum-split s n))
          (+-preserves-0≤ (0≤s n) (partial-sums-0≤ s 0≤s n))
