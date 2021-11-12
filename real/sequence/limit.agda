{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit where

open import base
open import real
open import real.interval
open import nat
open import truncation
open import rational
open import rational.proper-interval
open import sequence

private
  Seq : Type₁
  Seq = Sequence ℝ

record isLimit (seq : Seq) (lim : ℝ) : Type ℓ-one where
  no-eta-equality
  field
    lower : (q : ℚ) -> (Real.L lim q) -> ∀Largeℕ (\m -> Real.L (seq m) q)
    upper : (q : ℚ) -> (Real.U lim q) -> ∀Largeℕ (\m -> Real.U (seq m) q)

  close : (i : Iℚ) -> (ℝ∈Iℚ lim i) -> ∀Largeℕ (\m -> ℝ∈Iℚ (seq m) i)
  close (Iℚ-cons l u l≤u) (l<lim , lim<u) =
    ∀Largeℕ-∩ (lower l l<lim) (upper u lim<u)
