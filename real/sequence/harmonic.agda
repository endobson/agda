{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.harmonic where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import nat.order
open import nat.properties
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-field.archimedean
open import ordered-semiring.archimedean.instances.rational
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational.open-interval
open import real
open import real.arithmetic.rational
open import real.open-interval
open import real.rational
open import real.sequence.limit
open import sequence
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

harmonic-sequence : Seq
harmonic-sequence n = (1/ℕ (suc n , tt))

0<harmonic-sequence : (n : ℕ) -> 0# < harmonic-sequence n
0<harmonic-sequence n = (0<1/ℕ (suc n , tt))

isLimit-harmonic-sequence : isLimit harmonic-sequence 0#
isLimit-harmonic-sequence = close->isLimit f
  where
  f : (qi : Iℚ) -> ℝ∈Iℚ 0# qi -> ∀Largeℕ (\m -> ℝ∈Iℚ (harmonic-sequence m) qi)
  f qi@(Iℚ-cons l u _) (l<0 , 0<u) = ∥-map handle (small-1/ℕ (_ , U->ℚ< 0<u))
    where
    handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m < u) -> ∀Largeℕ' (\m -> ℝ∈Iℚ (harmonic-sequence m) qi)
    handle (m⁺@(m@(suc m') , _) , 1/m<u) = m' , g
      where
      g : (n : ℕ) -> (m' ≤ n) -> ℝ∈Iℚ (harmonic-sequence n) qi
      g n m'≤n =
        ℝ<->L (trans-< (L->ℝ< l<0) (0<harmonic-sequence n)) ,
        ℝ<->U (trans-≤-< (1/ℕ-flips-≤ m⁺ (suc n , _) (suc-≤ m'≤n))
                         (trans-=-< (sym (Semiringʰ-preserves-1/ℕ Semiringʰ-ℚ->ℝ m⁺))
                                    (ℚ->ℝ-preserves-< 1/m<u)))
