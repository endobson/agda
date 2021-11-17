{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.harmonic where

open import additive-group
open import additive-group.instances.real
open import base
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import nat.properties
open import real.interval
open import real.rational
open import real.sequence.limit
open import sequence
open import truncation
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real

import nat.order as no

private
  Seq : Type₁
  Seq = Sequence ℝ

harmonic-sequence : Seq
harmonic-sequence n = ℚ->ℝ (1/ℕ (suc n , tt))

0<harmonic-sequence : (n : ℕ) -> 0# < harmonic-sequence n
0<harmonic-sequence n = ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc n , tt))

isLimit-harmonic-sequence : isLimit harmonic-sequence 0#
isLimit-harmonic-sequence = close->isLimit f
  where
  f : (qi : Iℚ) -> ℝ∈Iℚ 0# qi -> ∀Largeℕ (\m -> ℝ∈Iℚ (harmonic-sequence m) qi)
  f qi@(Iℚ-cons l u _) (l<0 , 0<u) = ∥-map handle (small-1/ℕ (_ , U->ℚ< 0<u))
    where
    handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m < u) -> ∀Largeℕ' (\m -> ℝ∈Iℚ (harmonic-sequence m) qi)
    handle ((m@(suc m') , _) , 1/m<u) = m' , g
      where
      g : (n : ℕ) -> (m' ≤ n) -> ℝ∈Iℚ (harmonic-sequence n) qi
      g n m'≤n = ℝ<->L l (harmonic-sequence n) (trans-< (L->ℝ< l<0) (0<harmonic-sequence n)) ,
                 ℝ<->U (harmonic-sequence n) u 
                   (ℚ->ℝ-preserves-< _ _ (trans-≤-< (1/ℕ-flips-≤ (suc m' , _) (suc n , _) (no.suc-≤ m'≤n))
                                                    1/m<u))
