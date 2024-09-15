{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential-series where

open import additive-group
open import additive-group.instances.real
open import base
open import combinatorics.factorial
open import equality
open import functions
open import heyting-field.instances.real
open import metric-space.continuous
open import metric-space.instances.real
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.archimedean.instances.real
open import ordered-semiring.initial
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.distance
open import real.sequence.limit
open import real.sequence.ratio-test
open import real.series
open import real.subspace
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import sequence
open import sequence.partial-sums
open import sigma.base
open import subset.subspace
open import truncation

exp-terms : ℝ -> Sequence ℝ
exp-terms x n = (1/ℕ (factorial⁺ n)) * (x ^ℕ n)

opaque
  -- Since (exp-terms z 1) doesn't 'remember' z, this formulation works with out having
  -- to provide an explicit 'z'.
  exp-term0 : (1/ℕ (factorial⁺ 0)) * 1# == 1#
  exp-term0 = *-left (sym *-left-one >=>
                       *-left (sym ℕ->Semiring-preserves-1#) >=>
                       ∃!-prop (∃!1/ℕ (1 , tt))) >=>
               *-left-one

  exp-term1 : {z : ℝ} -> exp-terms z 1 == z
  exp-term1 = *-left (sym *-left-one >=>
                      *-left (sym ℕ->Semiring-preserves-1#) >=>
                      ∃!-prop (∃!1/ℕ (1 , tt))) >=>
              *-left-one >=> *-right-one

private
  exponential-ratios : ℝ -> Sequence ℝ
  exponential-ratios x n = (1/ℕ (suc n , tt)) * x

  exponential-series : ℝ -> Sequence ℝ
  exponential-series x = partial-sums (exp-terms x)

opaque
  isRatioSeq-exponential : (x : ℝ) -> isRatioSeq (exp-terms x) (exponential-ratios x)
  isRatioSeq-exponential x .isRatioSeq.f n =
    *-swap >=>
    *-cong *-commute *-commute >=>
    *-left (sym (1/ℕ-preserves-* (suc n , tt) (factorial⁺ n)) >=>
            cong 1/ℕ (ΣProp-path isPropPos' refl))

  isLimit-exponential-ratio : (x : ℝ) -> isLimit (abs ∘ exponential-ratios x) 0#
  isLimit-exponential-ratio x = distance<ε->isLimit f
    where
    f : (ε : ℝ⁺) -> ∀Largeℕ (\n -> εClose ε  0# (abs (exponential-ratios x n)))
    f ε⁺@(ε , 0<ε) = ∥-map handle (strong-archimedean-property 0<ε)
      where
      handle : Σ[ n ∈ ℕ ] (abs x < (ℕ->Semiring n * ε)) ->
               ∀Largeℕ' (\n -> εClose ε⁺ 0# (abs (exponential-ratios x n)))
      handle (n , ax<nε) = suc n , g
        where
        sn⁺ : Nat⁺
        sn⁺ = suc n , tt
        ax/sn<ε : ((1/ℕ (suc n , tt)) * abs x) < ε
        ax/sn<ε = trans-<-= ax/sn<snε/sn simplify-snε
          where
          nℝ : ℝ
          nℝ = ℕ->Semiring n
          snℝ : ℝ
          snℝ = ℕ->Semiring (suc n)
          nε<snε : (nℝ * ε) < (snℝ * ε)
          nε<snε = *₂-preserves-< (ℕ->Semiring-preserves-< refl-≤) 0<ε
          ax/sn<snε/sn : ((1/ℕ sn⁺) * abs x) < ((1/ℕ sn⁺) * (snℝ * ε))
          ax/sn<snε/sn = *₁-preserves-< (0<1/ℕ _) (trans-< ax<nε nε<snε)
          simplify-snε : ((1/ℕ sn⁺) * (snℝ * ε)) == ε
          simplify-snε = sym *-assoc >=> *-left (*-commute >=> (∃!-prop (∃!1/ℕ _))) >=> *-left-one

        g : (m : ℕ) (sn≤m : suc n ≤ m) -> εClose ε⁺ 0# (abs (exponential-ratios x m))
        g m sn≤m = distance0-<⁺ abs-0≤ abs-ratio<ε -- (max-least-< ratio<ε -ratio<ε)
          where
          abs-ratio<ε : abs (exponential-ratios x m) < ε
          abs-ratio<ε = trans-≤-< abs-ratio≤ ax/sn<ε
            where
            abs-ratio≤ : abs (exponential-ratios x m) ≤ (1/ℕ (suc n , tt) * abs x)
            abs-ratio≤ =
              trans-=-≤ abs-distrib-*
                (*₂-preserves-≤ (trans-=-≤ (abs-0≤-path (weaken-< (0<1/ℕ _)))
                                           (weaken-< (1/ℕ-flips-< _ _ (suc-≤ sn≤m))))
                                abs-0≤ )

  isAbsConvergentSeries-exponential : (x : ℝ) -> isAbsConvergentSeries (exp-terms x)
  isAbsConvergentSeries-exponential x =
    ratio-test (_ , trans-=-< (abs-0≤-path refl-≤) 0<1)
      (isRatioSeq-exponential x) (isLimit-exponential-ratio x)

exp : ℝ -> ℝ
exp x = fst (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-exponential x))

isLimit-exp : ∀ x -> isLimit (exponential-series x) (exp x)
isLimit-exp x = snd (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-exponential x))
