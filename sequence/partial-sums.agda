{-# OPTIONS --cubical --safe --exact-split #-}

module sequence.partial-sums where

open import additive-group
open import additive-group.instances.nat
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
open import order.instances.nat
open import ordered-additive-group
open import relation
open import sequence

module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}  where
  private
    Seq : Type ℓD
    Seq = Sequence D

  partial-sums : Seq -> Seq
  partial-sums s n = finiteSum (\ ((i , _) : Fin n) -> s i)

  abstract
    partial-sums-cons : (x : D) (s : Seq) (n : ℕ) ->
      partial-sums (seq-cons x s) (suc n) == x + partial-sums s n
    partial-sums-cons x s zero =
     finiteMerge-Fin1 _ _ >=>
     sym +-right-zero >=>
     +-right (sym (finiteMerge-Fin0 _ _))
    partial-sums-cons x s (suc n) = finiteMerge-FinSuc _ _

    partial-sums-split : (s : Seq) (n : ℕ) -> (partial-sums s (suc n)) == s n + partial-sums s n
    partial-sums-split s zero =
      finiteMerge-Fin1 _ _ >=>
      sym +-right-zero >=>
      +-right (sym (finiteMerge-Fin0 _ _))
    partial-sums-split s (suc n) =
      finiteMerge-FinSuc _ _ >=>
      +-right (partial-sums-split (drop1 s) n) >=>
      sym +-assoc >=>
      +-left +-commute >=>
      +-assoc >=>
      +-right (sym (finiteMerge-FinSuc _ _))

    partial-sums-dropN : (s : Seq) (n : ℕ) (i : ℕ) ->
      partial-sums s n + partial-sums (dropN n s) i == partial-sums s (n + i)
    partial-sums-dropN s n zero =
      +-right (finiteMerge-Fin0 _ _) >=> +-right-zero >=>
      cong (partial-sums s) (sym +-right-zero)
    partial-sums-dropN s n (suc i) =
      +-right (partial-sums-split (dropN n s) i) >=>
      sym +-assoc >=>
      +-left +-commute >=>
      +-assoc >=>
      +-right (partial-sums-dropN s n i) >=>
      sym (partial-sums-split s (n + i)) >=>
      cong (partial-sums s) (sym +'-right-suc)

    module _ {{AG : AdditiveGroup ACM}} where
      diff-partial-sums : (s : Seq) (n m : ℕ) -> (lt : n ≤ m) ->
        diff (partial-sums s n) (partial-sums s m) == partial-sums (dropN n s) ⟨ lt ⟩
      diff-partial-sums s n m (j , p) =
        +-left (cong (partial-sums s) (sym p >=> +-commuteᵉ j n) >=>
                sym (partial-sums-dropN s n j) >=>
                +-commute) >=>
        +-assoc >=>
        +-right +-inverse >=>
        +-right-zero




module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤} {ACM : AdditiveCommMonoid D}
         {PO : isPartialOrder D≤}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
          where
  private
    instance
      IACM = ACM
      IPO = PO

    Seq : Type ℓD
    Seq = Sequence D

  abstract
    partial-sums-0≤ :
      (s : Seq) -> ((n : ℕ) -> 0# ≤ s n) -> (n : ℕ) -> 0# ≤ partial-sums s n
    partial-sums-0≤ s 0≤s zero =
      subst2 _≤_ (finiteMerge-Fin0 _ _) refl refl-≤
    partial-sums-0≤ s 0≤s (suc n) =
      subst (0# ≤_) (sym (partial-sums-split s n))
            (+-preserves-0≤ (0≤s n) (partial-sums-0≤ s 0≤s n))

    partial-sums-≤ :
      {s1 s2 : Seq} -> ((n : ℕ) -> s1 n ≤ s2 n) -> (n : ℕ) -> partial-sums s1 n ≤ partial-sums s2 n
    partial-sums-≤ s1≤s2 zero =
      path-≤ (finiteMerge-Fin0 _ _ >=> sym (finiteMerge-Fin0 _ _))
    partial-sums-≤ {s1} {s2} s1≤s2 (suc n) =
      subst2 _≤_ (sym (partial-sums-split s1 n)) (sym (partial-sums-split s2 n))
        (+-preserves-≤ (s1≤s2 n) (partial-sums-≤ s1≤s2 n))
