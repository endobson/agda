{-# OPTIONS --cubical --safe --exact-split #-}

module real.infinite-sum.base where


open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import combinatorics.triangle-numbers
open import cubical
open import decision
open import equality-path
open import equivalence
open import equivalence.base
open import fin.sum-pair
open import functions
open import funext
open import hlevel.base
open import hlevel.sigma
open import isomorphism
open import nat
open import nat.iteration
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-semiring.instances.real
open import real
open import real.infinite-sum
open import real.infinite-sum.triangle
open import real.infinite-sum.cauchy-triangle
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import real.sequence.limit.order
open import real.sequence.limit.subsequence
open import real.series
open import real.series.base
open import real.series.cauchy-product
open import relation
open import ring.implementations.real
open import semiring
open import sequence
open import sequence.partial-sums
open import sequence.subsequence
open import sigma
open import sigma.base
open import truncation


opaque
  isAbsolutelyConvergent->isInfiniteSum : {s : ℕ -> ℝ} {v : ℝ} ->
    (isAbsConvergentSeries s) -> isLimit (partial-sums s) v -> isInfiniteSum s v
  isAbsolutelyConvergent->isInfiniteSum {s} {v} ac lim =
    subst (isInfiniteSum s) p (snd inf-sum)
    where
    inf-sum : hasInfiniteSum s
    inf-sum = absolutely-convergent->hasInfiniteSum (idEquiv ℕ) ac

    p : ⟨ inf-sum ⟩ == v
    p = cong fst (isProp-isConvergentSequence
                   (fst inf-sum , (isInfiniteSum.limit (snd inf-sum) (idEquiv ℕ)))
                   (v , lim))


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {s₁ : A -> ℝ} {s₂ : B -> ℝ} {v₁ v₂ : ℝ}
  (sum₁ : isInfiniteSum s₁ v₁)
  (sum₂ : isInfiniteSum s₂ v₂)
  where
  private
    s₃ : A × B -> ℝ
    s₃ (a , b) = s₁ a * s₂ b
    module _
      ((eq₁ , ac₁) : Σ[ eq₁ ∈ (A ≃ ℕ) ] (isAbsConvergentSeries (s₁ ∘ eqInv eq₁)))
      ((eq₂ , ac₂) : Σ[ eq₂ ∈ (B ≃ ℕ) ] (isAbsConvergentSeries (s₂ ∘ eqInv eq₂)))
      where
      r₁ : ℕ -> ℝ
      r₁ = s₁ ∘ eqInv eq₁
      r₂ : ℕ -> ℝ
      r₂ = s₂ ∘ eqInv eq₂

      ac₁' : isAbsConvergentSeries (abs ∘ r₁)
      ac₁' = subst isConvergentSeries ar₁=aar₁ ac₁
        where
        ar₁=aar₁ : abs ∘ r₁ == abs ∘ abs ∘ r₁
        ar₁=aar₁ = funExt (\_ -> sym (abs-0≤-path abs-0≤))
      ac₂' : isAbsConvergentSeries (abs ∘ r₂)
      ac₂' = subst isConvergentSeries ar₂=aar₂ ac₂
        where
        ar₂=aar₂ : abs ∘ r₂ == abs ∘ abs ∘ r₂
        ar₂=aar₂ = funExt (\_ -> sym (abs-0≤-path abs-0≤))


      eqℕ : (ℕ × ℕ) ≃ ℕ
      eqℕ = triangle-encode , isEquiv-triangle-encode

      eq× : (A × B) ≃ ℕ
      eq× = (×-equiv eq₁ eq₂) >eq> eqℕ


      r₃ : ℕ -> ℝ
      r₃ = (\{ (i , j) -> (r₁ i * r₂ j)}) ∘ eqInv eqℕ

      r₄ : ℕ -> ℝ
      r₄ = cauchy-product r₁ r₂

      r₅ : ℕ -> ℝ
      r₅ = cauchy-product (abs ∘ r₁) (abs ∘ r₂)


      isLimit-r₄ : isLimit (partial-sums r₄) (v₁ * v₂)
      isLimit-r₄ =
        isLimit-cauchy-product
          (isInfiniteSum.limit sum₁ eq₁)
          (isInfiniteSum.limit sum₂ eq₂)
          ac₁

      isConv-r₅ : isConvergentSeries r₅
      isConv-r₅ = _ , isLimit-cauchy-product (snd ac₁) (snd ac₂) ac₁'

      isSub-r₃r₄ : isSubsequenceOf (partial-sums r₃) (partial-sums r₄)
      isSub-r₃r₄ = isSubsequenceOf-s₄s₃ ac₁ ac₂


      isSub-ar₃r₅' : isSubsequenceOf (partial-sums ((\{ (i , j) -> (abs (r₁ i) * abs (r₂ j))}) ∘ eqInv eqℕ))
                                     (partial-sums r₅)
      isSub-ar₃r₅' = isSubsequenceOf-s₄s₃ ac₁' ac₂'

      isSub-ar₃r₅ : isSubsequenceOf (partial-sums (abs ∘ r₃)) (partial-sums r₅)
      isSub-ar₃r₅ =
        subst (\s -> isSubsequenceOf (partial-sums s) (partial-sums r₅)) p isSub-ar₃r₅'
        where
        p : ((\{ (i , j) -> (abs (r₁ i) * abs (r₂ j))}) ∘ eqInv eqℕ) ==
            (abs ∘ r₃)
        p = funExt (\i -> sym abs-distrib-*)


      aconv-r₃ : isConvergentSeries ((\{ (i , j) -> abs (r₁ i * r₂ j)}) ∘ eqInv eqℕ)
      aconv-r₃ =
        _ ,
        isNonDecreasing-isLimit-Subsequence->isLimit
          (partial-sums-nondecreasing (\_ -> abs-0≤))
          isSub-ar₃r₅
          (snd isConv-r₅)

      conv-r₃ : isConvergentSeries ((\{ (i , j) -> (r₁ i * r₂ j)}) ∘ eqInv eqℕ)
      conv-r₃ = isAbsConvergentSeries->isConvergentSeries aconv-r₃




      isLimit-r₃ : isLimit (partial-sums r₃) (v₁ * v₂)
      isLimit-r₃ = isLimit-Subsequence->isLimit conv-r₃ isSub-r₃r₄ isLimit-r₄


      hasInfiniteSum-s₃ : hasInfiniteSum s₃
      hasInfiniteSum-s₃ = absolutely-convergent->hasInfiniteSum eq× aconv-r₃

      isInfiniteSum-s₃ : isInfiniteSum s₃ (v₁ * v₂)
      isInfiniteSum-s₃ = subst (isInfiniteSum s₃) v-path (snd hasInfiniteSum-s₃)
        where
        v-path : fst hasInfiniteSum-s₃ == (v₁ * v₂)
        v-path =
          cong fst (isProp-isConvergentSequence (_ , lim) (_ , isLimit-r₃))
          where
          lim : isLimit (partial-sums (s₃ ∘ eqInv eq×)) (fst hasInfiniteSum-s₃)
          lim = isInfiniteSum.limit (snd hasInfiniteSum-s₃) eq×


  opaque
    isInfiniteSum-× : isInfiniteSum (\ ((a , b) : A × B) -> s₁ a * s₂ b) (v₁ * v₂)
    isInfiniteSum-× =
      unsquash isProp-isInfiniteSum
        (∥-map2 isInfiniteSum-s₃
          (isInfiniteSum.absolutely-convergent sum₁)
          (isInfiniteSum.absolutely-convergent sum₂))
