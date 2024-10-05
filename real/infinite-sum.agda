{-# OPTIONS --cubical --safe --exact-split #-}

module real.infinite-sum where

open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import isomorphism
open import nat
open import real
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import real.series.base
open import sequence.partial-sums
open import sequence.permutation
open import sigma.base
open import truncation

module _ {ℓA : Level} {A : Type ℓA} where
  record isInfiniteSum (s : A -> ℝ) (v : ℝ) : Type (ℓ-max ℓA ℓ-one) where
    field
      absolutely-convergent : ∃[ eq ∈ (A ≃ ℕ) ] isAbsConvergentSeries (s ∘ eqInv eq)
      limit : ∀ (eq : A ≃ ℕ) -> isLimit (partial-sums (s ∘ eqInv eq)) v

  hasInfiniteSum : (s : A -> ℝ) -> Type (ℓ-max ℓA ℓ-one)
  hasInfiniteSum s = Σ[ v ∈ ℝ ] (isInfiniteSum s v)

  opaque
    isProp-isInfiniteSum : {s : A -> ℝ} {v : ℝ} -> isProp (isInfiniteSum s v)
    isProp-isInfiniteSum sum1 sum2 i = record
      { absolutely-convergent = squash (isInfiniteSum.absolutely-convergent sum1)
                                       (isInfiniteSum.absolutely-convergent sum2) i
      ; limit = isPropΠ (\_ -> isProp-isLimit) (isInfiniteSum.limit sum1)
                                               (isInfiniteSum.limit sum2) i
      }

    isProp-hasInfiniteSum : {s : A -> ℝ} -> isProp (hasInfiniteSum s)
    isProp-hasInfiniteSum {s} (v1 , sum1) (v2 , sum2) =
      ΣProp-path isProp-isInfiniteSum v-path
      where
      v-path : v1 == v2
      v-path = unsquash (isSet-ℝ v1 v2)
        (∥-map (\ (eq , _) -> cong fst (isProp-isConvergentSeries (_ , isInfiniteSum.limit sum1 eq)
                                                                  (_ , isInfiniteSum.limit sum2 eq)))
          (isInfiniteSum.absolutely-convergent sum1))


    absolutely-convergent->hasInfiniteSum : {s : A -> ℝ}
      (eq : A ≃ ℕ) -> isAbsConvergentSeries (s ∘ eqInv eq) -> hasInfiniteSum s
    absolutely-convergent->hasInfiniteSum {s} eq1 absConv = (fst conv) , record
      { absolutely-convergent = ∣ eq1 , absConv ∣
      ; limit = limit
      }
      where
      conv : isConvergentSeries (s ∘ eqInv eq1)
      conv = isAbsConvergentSeries->isConvergentSeries absConv

      limit : ∀ (eq2 : A ≃ ℕ) -> isLimit (partial-sums (s ∘ eqInv eq2)) (fst conv)
      limit eq2 =
        subst2 isLimit (cong partial-sums s-path) refl
          (permute-preserves-limit-partial-sums p absConv (snd conv))
        where
        p : Iso ℕ ℕ
        p = equivToIso ((equiv⁻¹ eq2) >eq> eq1)

        s-path : permute-seq p (s ∘ eqInv eq1) == (s ∘ eqInv eq2)
        s-path = funExt (\i -> cong s (eqRet eq1 (eqInv eq2 i)))
