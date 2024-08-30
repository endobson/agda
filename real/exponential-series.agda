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

private
  Seq : Type₁
  Seq = Sequence ℝ

  exponential-sequence : ℝ -> Seq
  exponential-sequence x n = (1/ℕ (factorial⁺ n)) * (x ^ℕ n)

  exponential-ratios : ℝ -> Seq
  exponential-ratios x n = (1/ℕ (suc n , tt)) * x

  exponential-series : ℝ -> Seq
  exponential-series x = partial-sums (exponential-sequence x)

opaque
  isRatioSeq-exponential : (x : ℝ) -> isRatioSeq (exponential-sequence x) (exponential-ratios x)
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

  isAbsConvergentSeries-exponential : (x : ℝ) -> isAbsConvergentSeries (exponential-sequence x)
  isAbsConvergentSeries-exponential x =
    ratio-test (isRatioSeq-exponential x) (isLimit-exponential-ratio x) refl-≤ 0<1

exp : ℝ -> ℝ
exp x = fst (isAbsConvergentSeries-exponential x)
