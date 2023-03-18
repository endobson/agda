{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.absolute-convergence where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import finset.instances
open import finsum.absolute-value
open import functions
open import nat
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import rational.order
open import real
open import real.epsilon-bounded
open import real.sequence.cauchy
open import real.series
open import sequence
open import sequence.partial-sums
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

abstract
  AbsConvergentSeries->ConvergentSeries :
    {s : Seq} -> isAbsConvergentSeries s -> isConvergentSeries s
  AbsConvergentSeries->ConvergentSeries {s} isConv =
    isCauchy->isConvergentSequence
      (\ε -> (∥-map (\{ (n , f) -> ans ε n f }) (isConvergentSequence->isCauchy isConv ε)))
    where
    module _ (ε⁺ : ℚ⁺) (n : ℕ) (f : (m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                                    εBounded ⟨ ε⁺ ⟩ (diff (partial-sums (abs ∘ s) m₁)
                                                     (partial-sums (abs ∘ s) m₂)))
      where
      ε = ⟨ ε⁺ ⟩
      module _ (m1 m2 : Nat) (m1≤m2 : m1 ≤ m2) (n≤m1 : n ≤ m1) (n≤m2 : n ≤ m2) where
         εB-psums-abs : εBounded ε (diff (partial-sums (abs ∘ s) m1) (partial-sums (abs ∘ s) m2))
         εB-psums-abs = f m1 m2 n≤m1 n≤m2

         path1 : (diff (partial-sums (abs ∘ s) m1) (partial-sums (abs ∘ s) m2)) ==
                 (partial-sums (dropN m1 (abs ∘ s)) (fst m1≤m2))
         path1 = diff-partial-sums (abs ∘ s) m1 m2 m1≤m2

         lt1 : abs (partial-sums (dropN m1 s) (fst m1≤m2)) ≤
               (partial-sums (dropN m1 (abs ∘ s)) (fst m1≤m2))
         lt1 = finiteSum-abs≤

         path2 : (diff (partial-sums s m1) (partial-sums s m2)) ==
                 (partial-sums (dropN m1 s) (fst m1≤m2))
         path2 = diff-partial-sums s m1 m2 m1≤m2

         εB-psums : εBounded ε (diff (partial-sums s m1) (partial-sums s m2))
         εB-psums =
           subst (εBounded ε) (sym path2)
             (εBounded-abs≤ lt1 (subst (εBounded ε) path1 εB-psums-abs))

      ans : Σ[ n ∈ ℕ ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                        εBounded ε (diff (partial-sums s m₁) (partial-sums s m₂)))
      ans = n , \m1 m2 n≤m1 n≤m2 -> case (split-< m1 m2) of
                  \{ (inj-l m1<m2) -> εB-psums m1 m2 (weaken-< m1<m2) n≤m1 n≤m2
                   ; (inj-r m2≤m1) ->
                      subst (εBounded ε) (sym diff-anticommute)
                        (εBounded-- _ (εB-psums m2 m1 m2≤m1 n≤m2 n≤m1))
                   }
