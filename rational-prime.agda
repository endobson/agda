{-# OPTIONS --cubical --safe --exact-split #-}

module rational-prime where

open import rational
open import equality
open import prime
open import int
open import base
open import ring.implementations.rational

module rr = RationalRing

module _ (p : Prime') where
  private
    p' = ⟨ p ⟩
    pℤ = ℕ->ℤ p'
    pℚ = ℕ->ℚ p'

    isNonZeroℚ-p : isNonZeroℚ pℚ
    isNonZeroℚ-p = Pos'->NonZeroℚ (Prime'.pos p)

    isUnit-p : rr.isUnit pℚ
    isUnit-p = rr.is-unit pℚ 1/pℚ (r*-commute pℚ 1/pℚ >=> r1/-inverse pℚ ℚInv-p)
      where
      ℚInv-p = (isNonZeroℚ->ℚInv isNonZeroℚ-p)
      1/pℚ = (r1/ pℚ ℚInv-p)

    pℚU : rr.Unit
    pℚU = pℚ , isUnit-p

  ℚUnit-prime : rr.Unit
  ℚUnit-prime = pℚU


  prime-powerℚ' : ℤ -> rr.Unit
  prime-powerℚ' x = (pℚU rr.u^ℤ x)

  prime-powerℚ : ℤ -> ℚ
  prime-powerℚ x = fst (prime-powerℚ' x)

  ℕ->ℚ-prime-power : (n : Nat) -> ℕ->ℚ (prime-power p n) == prime-powerℚ (int n)
  ℕ->ℚ-prime-power zero    = refl
  ℕ->ℚ-prime-power (suc n) =
    Semiringʰ-ℕ->ℚ.preserves-* p' (prime-power p n) >=>
    cong (pℚ rr.*_) (ℕ->ℚ-prime-power n)
