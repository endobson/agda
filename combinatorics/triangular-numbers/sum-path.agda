{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.triangular-numbers.sum-path where

open import additive-group
open import additive-group.instances.nat
open import base
open import combinatorics.binomial-coefficients
open import combinatorics.triangular-numbers
open import equality-path
open import equivalence
open import fin
open import fin.sum-pair
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import finite-commutative-monoid.sum-pair
open import finset.instances
open import finset.instances.sum-pair
open import finsum
open import finsum.cardinality
open import isomorphism
open import maybe
open import nat
open import semiring
open import semiring.initial
open import semiring.instances.nat

private
  Fin-Maybe-eq' : (n : Nat) -> Fin (suc n) ≃ Maybe (Fin n)
  Fin-Maybe-eq' n = isoToEquiv i
    where
    open Iso
    i : Iso (Fin (suc n)) (Maybe (Fin n))
    i .fun (i , (zero , p)) = nothing
    i .fun (i , (suc j , p)) = just (i , (j , cong pred p))
    i .inv nothing     = max-fin
    i .inv (just j)    = inc-fin j
    i .rightInv nothing    = refl
    i .rightInv (just j)   = cong just (fin-i-path refl)
    i .leftInv (i , (zero  , p)) = fin-i-path (cong pred (sym p))
    i .leftInv (i , (suc j , p)) = fin-i-path refl


private
  triangular-number-rec : Nat -> Nat
  triangular-number-rec zero = zero
  triangular-number-rec (suc n) = suc n + triangular-number-rec n

  triangular-number-rec-path : ∀ n -> triangular-number-rec n == triangular-number n
  triangular-number-rec-path zero = refl
  triangular-number-rec-path (suc zero) = refl
  triangular-number-rec-path (suc n@(suc _)) =
    cong (suc n +_) (triangular-number-rec-path n) >=>
    +-commuteᵉ (suc n) (triangular-number n) >=>
    cong (triangular-number n +_) (sym (binomial-coeff'-one₂ n))

  triangular-number-sum-path' : ∀ n ->
    finiteSum (\ (p : (FinPair+ n)) -> FinPair+.i p) == triangular-number n
  triangular-number-sum-path' zero = finiteMerge-isContr _ isContr-FinPair+-0 _
  triangular-number-sum-path' (suc n) =
    finiteMerge-FinPair+-split₂ _ _ >=>
    +-right (triangular-number-sum-path' n >=> sym (triangular-number-rec-path n)) >=>
    triangular-number-rec-path (suc n)

  triangular-number-sum-path'2 : ∀ n ->
    finiteSum (\ ((i , _) : (Fin (suc n))) -> i) == triangular-number n
  triangular-number-sum-path'2 n =
    finiteMerge-convert-iso _ FinPair+-Fin-Iso _ >=>
    (triangular-number-sum-path' n)

  inner-reorg : ∀ n ->
    finiteSum (\ ((i , _) : (Fin (suc n))) -> i) ==
    finiteSum (\ ((i , _) : (Fin n)) -> (suc i))
  inner-reorg n =
    finiteMerge-convert _ (equiv⁻¹ (Fin-Maybe-eq' n)) _ >=>
    finiteMerge-Maybe _ _ >=>
    cong (_+ finiteSum (\ ((i , _) : (Fin n)) -> i))
      (sym finiteSum-one) >=>
    sym (finiteMerge-split _)

opaque
  triangular-number-sum-path : ∀ n ->
    finiteSum (\ ((i , _) : (Fin n)) -> (suc i)) == triangular-number n
  triangular-number-sum-path n =
    sym (inner-reorg n) >=> triangular-number-sum-path'2 n
