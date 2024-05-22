{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponetial-series2 where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import factorial
open import functions
open import integral-domain.instances.real
open import nat
open import nat.order
open import order
open import order.instances.rational
open import order.instances.real
open import order.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-semiring.archimedean
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.archimedean.instances.real
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import ordered-semiring.non-trivial
open import ordered-semiring.non-trivial.instances.rational
open import ordered-semiring.non-trivial.instances.real
open import rational
open import rational.integral-domain
open import rational.order
open import real
open import real.epsilon-bounded
open import real.arithmetic.rational
open import real.rational
open import real.series
open import real.sequence.ratio-test
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import ring.implementations.real
open import semiring
open import sigma.base
open import semiring.initial
open import sequence
open import sequence.partial-sums
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

  ℝ^ℕ : ℝ -> ℕ -> ℝ
  ℝ^ℕ x zero = 1#
  ℝ^ℕ x (suc n) = x * (ℝ^ℕ x n)

  exponential-sequence : ℝ -> Seq
  exponential-sequence x n = (ℝ^ℕ x n) * ℚ->ℝ (1/ℕ (factorial⁺ n))

  exponential-ratios : ℝ -> Seq
  exponential-ratios x n = x * ℚ->ℝ (1/ℕ (suc n , tt))

  exponential-series : ℝ -> Seq
  exponential-series x = partial-sums (exponential-sequence x)

isRatioSeq-exponential : (x : ℝ) -> isRatioSeq (exponential-sequence x) (exponential-ratios x)
isRatioSeq-exponential x .isRatioSeq.f n = *-swap >=> *-cong *-commute p
  where
  p = sym ℚ->ℝ-preserves-* >=>
      cong ℚ->ℝ (*-commute >=> sym (1/ℕ-preserves-* (suc n , tt) (factorial⁺ n)) >=>
                 cong 1/ℕ (ΣProp-path isPropPos' refl))

strong-archimedean-property : ∀ {a b : ℝ} -> 0# < b -> ∃[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))
strong-archimedean-property {a} {b} 0<b = ∥-bind handle (comparison-< _ a _ 0<b)
  where
  handle : (0# < a) ⊎ (a < b) -> ∃[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))
  handle (inj-l 0<a) = archimedean-property 0<a 0<b
  handle (inj-r a<b) = ∣ 1 , trans-<-= a<b (sym *-left-one >=> *-left (sym (ℕ->Semiring-ℝ-path 1))) ∣


isLimit-exponential-ratio : (x : ℝ) -> isLimit (abs ∘ exponential-ratios x) 0#
isLimit-exponential-ratio x = εBounded-diff->isLimit f
  where
  f : (ε : ℚ⁺) -> ∀Largeℕ (\n -> εBounded ⟨ ε ⟩ (diff 0# (abs (exponential-ratios x n))))
  f (ε , 0<ε) = ∥-map handle (strong-archimedean-property (ℚ->ℝ-preserves-< _ _ 0<ε))
    where
    handle : Σ[ n ∈ ℕ ] (abs x < (ℕ->Semiring n * (ℚ->ℝ ε))) ->
             ∀Largeℕ' (\n -> εBounded ε (diff 0# (abs (exponential-ratios x n))))
    handle (n , ax<nε) = n , g
      where
      ax/n<ε : (abs x * ℚ->ℝ (1/ℕ (suc n , tt))) < ℚ->ℝ ε
      ax/n<ε =
        trans-=-< (*-commute)
          (trans-<-= (*₁-preserves-< (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc n , tt)))
                                     (trans-< (trans-<-= ax<nε (*-left (ℕ->Semiring-ℝ-path n)))
                                              (*₂-preserves-<
                                                (ℚ->ℝ-preserves-< _ _ (ℕ->ℚ-preserves-order _ _ refl-≤))
                                                (ℚ->ℝ-preserves-< _ _ 0<ε))))
                     εp)
        where
        εp : (ℚ->ℝ (1/ℕ (suc n , tt)) * (ℕ->ℝ (suc n) * ℚ->ℝ ε)) == ℚ->ℝ ε
        εp = (sym *-assoc >=>
              *-left (sym ℚ->ℝ-preserves-* >=> (cong ℚ->ℝ (1/ℕ-ℕ-path (suc n , tt)))) >=>
              *-left-one)

      g : (m : ℕ) (n≤m : n ≤ m) -> εBounded ε (diff 0# (abs (exponential-ratios x m)))
      g m n≤m = subst (εBounded ε) (sym diff-step >=> +-left-zero)
                  (ℝ<->L -ε<abs-ratio , ℝ<->U abs-ratio<ε)
        where


        -ε<abs-ratio : (ℚ->ℝ (- ε)) < abs (exponential-ratios x m)
        -ε<abs-ratio = trans-<-≤ (ℚ->ℝ-preserves-< _ _ (minus-flips-0< 0<ε)) abs-0≤
        abs-ratio<ε : abs (exponential-ratios x m) < (ℚ->ℝ ε)
        abs-ratio<ε =
          trans-=-< (abs-distrib-* >=>
                     *-right (abs-0<-path (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ (suc m , tt)))))
                    (trans-≤-< (*₁-preserves-≤ abs-0≤ (ℚ->ℝ-preserves-≤ _ _
                                                        (1/ℕ-flips-≤ (suc n , tt) (suc m , tt)
                                                          (suc-≤ n≤m))))
                                ax/n<ε)

isAbsConvergentSeries-exponential : (x : ℝ) -> isAbsConvergentSeries (exponential-sequence x)
isAbsConvergentSeries-exponential x =
  ratio-test (isRatioSeq-exponential x) (isLimit-exponential-ratio x) refl-≤ 0<1

exp : ℝ -> ℝ
exp x = fst (isAbsConvergentSeries-exponential x)


private
  ℝFinite : (x : ℝ) -> ∃[ n ∈ ℕ ] (x < ℕ->ℝ n)
  ℝFinite x = ∥-bind handle (Real.located x _ _ 0<1)
    where
    handle : (Real.L x 0# ⊎ Real.U x 1#) -> ∃[ n ∈ ℕ ] (x < ℕ->ℝ n)
    handle (inj-r xU-1) = ∣ 1 , U->ℝ< xU-1 ∣
    handle (inj-l xL-0) = ∥-map handle2 (archimedean-property (L->ℝ< xL-0) 0<1)
      where
      handle2 : Σ[ n ∈ ℕ ] (x < (ℕ->Semiring n * 1#)) -> Σ[ n ∈ ℕ ] (x < ℕ->ℝ n)
      handle2 (n , x<n1) = n , trans-<-= x<n1 (*-right-one >=> ℕ->Semiring-ℝ-path n)

  -- exponential-sequence<geometric-sequence : (x : ℝ) ->
  --   ∀Largeℕ (\n -> exponential-sequence x n < geometric-sequence 1/2ℝ n)
  -- exponential-sequence<geometric-sequence = ∥-map handle (archimedean-property
