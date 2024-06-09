{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval.sequence where

open import additive-group
open import base
open import equality
open import functions
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import rational
open import rational.open-interval
open import rational.open-interval.containment
open import relation
open import sequence

ArbitrarilySmall : Pred (Sequence ℚ) ℓ-zero
ArbitrarilySmall s = ∀ ((ε , _) : ℚ⁺) -> ∀Largeℕ (\n -> s n < ε)

module _
  (s : Sequence Iℚ)
  (small : ArbitrarilySmall (i-width ∘ s))
  {q : ℚ}
  (q∈s : ∀ n -> ℚ∈Iℚ q (s n))
  where
  opaque
    ArbitrarilySmall->i⊂ : (i : Iℚ) -> (ℚ∈Iℚ q i) -> ∀Largeℕ (\n -> s n i⊂ i)
    ArbitrarilySmall->i⊂ i@(Iℚ-cons l u l<u) (l<q , q<u) =
      ∀Largeℕ-map handle (small w⁺)
      where
      w : ℚ
      w = min (diff l q) (diff q u)
      w⁺ : ℚ⁺
      w⁺ = w , min-greatest-< (diff-0<⁺ l<q) (diff-0<⁺ q<u)

      handle : {n : Nat} -> i-width (s n) < w -> s n i⊂ i
      handle {n} wsn<w = i⊂-cons l<lsn usn<u
        where
        lsn usn wsn : ℚ
        lsn = Iℚ.l (s n)
        usn = Iℚ.u (s n)
        wsn = diff lsn usn

        usn<q+w : usn < (q + w)
        usn<q+w = trans-=-< (sym diff-step) (+-preserves-< (proj₁ (q∈s n)) wsn<w)
        q+w≤u : (q + w) ≤ u
        q+w≤u = trans-≤-= (+₁-preserves-≤ min-≤-right) diff-step

        q-w<lsn : (q + (- w)) < lsn
        q-w<lsn = trans-< (+₂-preserves-< q<usn) usn-w<lsn
          where
          q<usn : q < usn
          q<usn = proj₂ (q∈s n)
          usn-w<lsn : (usn + (- w)) < lsn
          usn-w<lsn = trans-<-= (+₁-preserves-< (trans-<-= (minus-flips-< wsn<w) (sym diff-anticommute)))
                                diff-step
        l≤q-w : l ≤ (q + (- w))
        l≤q-w = trans-=-≤ (sym diff-step)
                          (+₁-preserves-≤ (trans-=-≤ diff-anticommute (minus-flips-≤ min-≤-left)))

        l<lsn : l < lsn
        l<lsn = trans-≤-< l≤q-w q-w<lsn
        usn<u : usn < u
        usn<u = trans-<-≤ usn<q+w q+w≤u
