{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.partition where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import fin
open import finset
open import nat
open import nat.order
open import order
open import ordered-semiring
open import ordered-semiring.instances.real
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import real
open import truncation
open import real.rational
open import rational
open import relation
open import fin-algebra
open import type-algebra
open import isomorphism
open import maybe

data PartitionIndex (n : Nat) : Type₀ where
  pi-low : PartitionIndex n
  pi-mid : Fin n -> PartitionIndex n
  pi-high : PartitionIndex n


PartitionIndex≃Fin : {n : Nat} -> PartitionIndex n ≃ Fin (suc (suc n))
PartitionIndex≃Fin {n} =
  (isoToEquiv i) >eq> (Maybe-eq (equiv⁻¹ (Fin-Maybe-eq _))) >eq> (equiv⁻¹ (Fin-Maybe-eq _))
  where
  open Iso
  i : Iso (PartitionIndex n) (Maybe (Maybe (Fin n)))
  i .fun pi-low = nothing
  i .fun (pi-mid idx) = (just (just idx))
  i .fun pi-high = (just nothing)
  i .inv nothing = pi-low
  i .inv (just nothing) = pi-high
  i .inv (just (just idx)) = pi-mid idx
  i .leftInv pi-low = refl
  i .leftInv (pi-mid idx) = refl
  i .leftInv pi-high = refl
  i .rightInv nothing = refl
  i .rightInv (just nothing) = refl
  i .rightInv (just (just idx)) = refl

instance
  FinSetStr-PartitionIndex : {n : Nat} -> FinSetStr (PartitionIndex n)
  FinSetStr-PartitionIndex .FinSetStr.isFin = ∣ _ , PartitionIndex≃Fin ∣

record Partition (a : ℝ) (b : ℝ) : Type₀ where
  no-eta-equality
  pattern
  field
    n : ℕ
    u : Fin (suc n) -> ℚ
    aU-u0 : Real.U a (u zero-fin)
    bL-un : Real.L b (u (n , refl-≤))
    u<u : (i : Fin n) -> u (inc-fin i) < u (suc-fin i)

  uℝ : Fin (suc n) -> ℝ
  uℝ i = ℚ->ℝ (u i)

  a<u0 : a < uℝ zero-fin
  a<u0 = U->ℝ< aU-u0

  un<b : (uℝ (n , refl-≤)) < b
  un<b = L->ℝ< bL-un

  uℝ<uℝ : (i : Fin n) -> uℝ (inc-fin i) < uℝ (suc-fin i)
  uℝ<uℝ i = ℚ->ℝ-preserves-< _ _ (u<u i)

  width : (i : PartitionIndex n) -> ℝ
  width (pi-low) = diff a (uℝ zero-fin)
  width (pi-mid i) = (diff (uℝ (inc-fin i)) (uℝ (suc-fin i)))
  width (pi-high) = diff (uℝ (n , refl-≤)) b

  abstract
    a<ui : (i : Fin (suc n)) -> a < uℝ i
    a<ui (i , lt) = handle i lt
      where
      handle : (i : Nat) -> (lt : i < suc n) -> a < uℝ (i , lt)
      handle zero lt = trans-<-= a<u0 (cong uℝ (fin-i-path refl))
      handle (suc i) lt =
        trans-< (handle i (trans-< refl-≤ lt))
                (subst2 _<_ (cong uℝ (fin-i-path refl)) (cong uℝ (fin-i-path refl))
                            (uℝ<uℝ (i , pred-≤ lt)))

    ui<b : (i : Fin (suc n)) -> uℝ i < b
    ui<b (i , j , path) = handle i j path
      where
      handle : (i j : Nat) -> (p : j + (suc i) == (suc n)) -> uℝ (i , j , p) < b
      handle i zero path = trans-=-< (cong uℝ (fin-i-path (cong pred path))) un<b
      handle i (suc j) path =
        trans-< (subst2 _<_ (cong uℝ (fin-i-path refl)) (cong uℝ (fin-i-path refl))
                            (uℝ<uℝ (i , j , cong pred path)))
                (handle (suc i) j (+'-right-suc >=> path))

    0<width : (i : PartitionIndex n) -> 0# < width i
    0<width pi-low = trans-=-< (sym +-inverse) (+₂-preserves-< a<u0)
    0<width (pi-mid i) = trans-=-< (sym +-inverse) (+₂-preserves-< (uℝ<uℝ i))
    0<width pi-high = trans-=-< (sym +-inverse) (+₂-preserves-< un<b)


PartitionSize< : {a b : ℝ} -> Rel (Partition a b) ℓ-zero
PartitionSize< p1 p2 = Partition.n p1 < Partition.n p2

WF-PartitionSize< : {a b : ℝ} -> WellFounded (PartitionSize< {a} {b})
WF-PartitionSize< {a} {b} p = rec p (Partition.n p) refl-≤
  where
  rec : (p : Partition a b) -> (n : Nat) -> (Partition.n p) ≤ n -> Acc PartitionSize< p
  rec p@(record {n = zero})    _    _  = acc (\y yn<0 -> bot-elim (zero-≮ yn<0))
  rec p@(record {n = (suc n)}) zero lt = bot-elim (zero-≮ lt)
  rec p@(record {n = (suc n)}) (suc n') lt =
    acc \p2 p2n<pn -> rec p2 n' (pred-≤ (trans-≤ p2n<pn lt))


partition->< : {a b : ℝ} -> Partition a b -> a < b
partition->< p =
  trans-< (Partition.a<ui p zero-fin) (Partition.ui<b p zero-fin)

isδFine : {a b : ℝ} (δ : ℝ) (p : Partition a b) -> Type₁
isδFine δ p = (i : PartitionIndex p.n) -> p.width i ≤ δ
  where
  module p = Partition p

weaken-isδFine : {a b : ℝ} {δ1 δ2 : ℝ} -> δ1 ≤ δ2 -> (p : Partition a b) ->
                          isδFine δ1 p -> isδFine δ2 p
weaken-isδFine δ1≤δ2 _ f i = trans-≤ (f i) δ1≤δ2
