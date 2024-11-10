{-# OPTIONS --cubical --safe --exact-split #-}

module hundred-theorems.theorem1 where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import hlevel
open import int
open import nat
open import nat.even-odd
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import prime
open import prime-div-count
open import rational
open import rational.integer
open import real
open import real.arithmetic.rational
open import real.arithmetic.sqrt
open import real.arithmetic.sqrt.base
open import real.irrational
open import real.rational
open import relation
open import ring
open import ring.implementations.int
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import semiring.instances.nat
open import subset.subspace
open import truncation

-- Sqrt of two is irrational.

private
  opaque
    no-sqrt2-ℕ : (a b : ℕ) -> Pos' b -> (a * a) != (2 * (b * b))
    no-sqrt2-ℕ a         zero      ()
    no-sqrt2-ℕ zero      b@(suc _) _ aa=2bb = zero-suc-absurd aa=2bb
    no-sqrt2-ℕ a@(suc _) b@(suc _) _ aa=2bb =
      Even->¬Odd (suc (n2 + n2)) (subst Even p e1) o2
      where
      2p : Prime'
      2p = 2 , 2-is-prime

      c1 : Σ[ n ∈ ℕ ] (PrimeDivCount 2p a n)
      c1 = compute-prime-div-count 2p (a , tt)
      c2 : Σ[ n ∈ ℕ ] (PrimeDivCount 2p b n)
      c2 = compute-prime-div-count 2p (b , tt)
      n1 n2 : ℕ
      n1 = fst c1
      n2 = fst c2

      c3 : PrimeDivCount 2p 2 1
      c3 = prime-power-div-count 2p 1

      c4 : PrimeDivCount 2p (a * a) (n1 + n1)
      c4 = *'-prime-div-count (snd c1) (snd c1)
      c5 : PrimeDivCount 2p (2 * (b * b)) (1 + (n2 + n2))
      c5 = *'-prime-div-count c3 (*'-prime-div-count (snd c2) (snd c2))

      p : (n1 + n1) == suc (n2 + n2)
      p = prime-div-count-unique (subst2 (PrimeDivCount 2p) aa=2bb refl c4) c5

      e1 : Even (n1 + n1)
      e1 = twice->Even n1
      o2 : Odd (suc (n2 + n2))
      o2 = twice->Even n2

    no-sqrt2-ℚ : (a : ℚ) -> (a * a) != 2#
    no-sqrt2-ℚ a aa=2 = unsquash isPropBot (∥-map handle (ℚ->split-ℤℕ⁺ a))
      where

      step3 : (d : ℕ) -> 2# * ((ℕ->ℚ d) * (ℕ->ℚ d)) == ℕ->ℚ (2# * (d * d))
      step3 d =
        *-cong (sym (Semiringʰ.preserves-+ Semiringʰ-ℕ->ℚ 1# 1#))
               (sym (Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ d d)) >=>
        (sym (Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ 2# (d * d)))

      handle : Σ[ n ∈ ℤ ] Σ[ (d , _) ∈ Nat⁺ ] (ℤ->ℚ n == a * ℕ->ℚ d) -> Bot
      handle ((nonneg n) , (d , pos-d) , n=a*d) =
        no-sqrt2-ℕ n d pos-d step5
        where
        step1 : ℕ->ℚ (n * n) == ℤ->ℚ ((nonneg n) * (nonneg n))
        step1 = cong ℤ->ℚ (Semiringʰ.preserves-* Semiringʰ-ℕ->ℤ n n)

        step2 : ℤ->ℚ ((nonneg n) * (nonneg n)) == 2# * ((ℕ->ℚ d) * (ℕ->ℚ d))
        step2 =
          Semiringʰ.preserves-* Semiringʰ-ℤ->ℚ (nonneg n) (nonneg n) >=>
          *-cong n=a*d n=a*d >=>
          *-swap >=>
          *-left aa=2

        step4 : ℕ->ℚ (n * n) == ℕ->ℚ (2# * (d * d))
        step4 = step1 >=> step2 >=> step3 d
        step5 : (n * n) == (2# * (d * d))
        step5 = nonneg-injective (isInjective-ℤ->ℚ step4)


      handle (nℤ@(neg n) , (d , pos-d) , n=a*d) =
        no-sqrt2-ℕ (suc n) d pos-d step5
        where
        step1 : ℕ->ℚ (suc n * suc n) == ℤ->ℚ ((neg n) * (neg n))
        step1 =
          cong ℤ->ℚ (
            Semiringʰ.preserves-* Semiringʰ-ℕ->ℤ (suc n) (suc n) >=>
            sym minus-extract-both)

        step2 : ℤ->ℚ ((neg n) * (neg n)) == 2# * ((ℕ->ℚ d) * (ℕ->ℚ d))
        step2 =
          Semiringʰ.preserves-* Semiringʰ-ℤ->ℚ (neg n) (neg n) >=>
          *-cong n=a*d n=a*d >=>
          *-swap >=>
          *-left aa=2

        step4 : ℕ->ℚ (suc n * suc n) == ℕ->ℚ (2# * (d * d))
        step4 = step1 >=> step2 >=> step3 d
        step5 : (suc n * suc n) == (2# * (d * d))
        step5 = nonneg-injective (isInjective-ℤ->ℚ step4)

isIrrational-sqrt2 : isIrrational (sqrtℝ (2# , (weaken-< 0<2)))
isIrrational-sqrt2 q = handle (split-< q 0#) (trichotomous-< (q * q) 2#)
  where
  opaque
    unfolding sqrtℝ
    1+1=2q : 1# + 1# == ℚ->ℝ 2#
    1+1=2q = sym ℚ->ℝ-preserves-+
    handle : (q < 0# ⊎ 0# ≤ q) -> Tri< (q * q) 2# -> (sqrtℝ (2# , (weaken-< 0<2))) # (ℚ->ℝ q)
    handle (inj-l q<0) _ = inj-r (L->ℝ< (inj-l q<0))
    handle (inj-r 0≤q) (tri< qq<2 _ _) =
      inj-r (L->ℝ< (inj-r (0≤q , subst2 Real.L (sym 1+1=2q) refl (ℚ<->L qq<2))))
    handle (inj-r 0≤q) (tri> _ _ 2<qq) =
      inj-l (U->ℝ< (0≤q , subst2 Real.U (sym 1+1=2q) refl (ℚ<->U 2<qq)))
    handle (inj-r 0≤q) (tri= _ qq=2 _) = bot-elim (no-sqrt2-ℚ q qq=2)
