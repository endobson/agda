{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.subsequence where


open import real.sequence.limit
open import sequence
open import real
open import real.order
open import base
open import nat
open import nat.order
open import order
open import additive-group
open import additive-group.instances.nat
open import order.instances.nat
open import order.minmax
open import order.minmax.instances.nat
open import order.instances.real
open import truncation
open import sequence.subsequence
open import rational
open import equality-path


private
  isLimit-Subsequence' : {s₁ s₂ : Sequence ℝ} {v : ℝ} ->
    isLimit s₁ v -> isSubsequenceOf' s₁ s₂ -> isLimit s₂ v
  isLimit-Subsequence' {s₁} {s₂} {v} lim (f , inc-f , p) = record
    { lower = lower
    ; upper = upper
    }
    where
    inf-f : ∀ i -> i ≤ f i
    inf-f zero = zero-≤
    inf-f (suc n) = trans-≤ (suc-≤ (inf-f n)) (inc-f n)

    lower : (q : ℚ) -> Real.L v q -> ∀Largeℕ (\m -> Real.L (s₂ m) q)
    lower q vL-q = ∥-map handle (isLimit.lower lim q vL-q)
      where
      handle : ∀Largeℕ' (\m -> Real.L (s₁ m) q) -> ∀Largeℕ' (\m -> Real.L (s₂ m) q)
      handle (n , L₁) = (n , (\i n≤i -> subst (\x -> Real.L x q) (p i) (L₁ (f i) (trans-≤ n≤i (inf-f i)))))
    upper : (q : ℚ) -> Real.U v q -> ∀Largeℕ (\m -> Real.U (s₂ m) q)
    upper q vU-q = ∥-map handle (isLimit.upper lim q vU-q)
      where
      handle : ∀Largeℕ' (\m -> Real.U (s₁ m) q) -> ∀Largeℕ' (\m -> Real.U (s₂ m) q)
      handle (n , U₁) = (n , (\i n≤i -> subst (\x -> Real.U x q) (p i) (U₁ (f i) (trans-≤ n≤i (inf-f i)))))


opaque
  isLimit-Subsequence : {s₁ s₂ : Sequence ℝ} {v : ℝ} ->
    isLimit s₁ v -> isSubsequenceOf s₁ s₂ -> isLimit s₂ v
  isLimit-Subsequence {s₁} {s₂} {v} lim ss =
    unsquash isProp-isLimit (∥-map (isLimit-Subsequence' lim) ss)


opaque
  isLimit-Subsequence->isLimit : {s₁ s₂ : Sequence ℝ} {v : ℝ} ->
    isConvergentSequence s₁ -> isSubsequenceOf s₁ s₂ -> isLimit s₂ v -> isLimit s₁ v
  isLimit-Subsequence->isLimit {s₁} {s₂} {v₂} (v₁ , lim₁) ss lim₂ =
    subst (isLimit s₁)
      (cong fst (isProp-isConvergentSequence (v₁ , (isLimit-Subsequence lim₁ ss)) (v₂ , lim₂)))
      lim₁

  isNonDecreasing-isLimit-Subsequence'->isLimit :
    {s₁ s₂ : Sequence ℝ} {v : ℝ} ->
    (∀ {i₁ i₂ : ℕ} -> i₁ ≤ i₂ -> s₁ i₁ ≤ s₁ i₂) ->
    isSubsequenceOf' s₁ s₂ -> isLimit s₂ v -> isLimit s₁ v
  isNonDecreasing-isLimit-Subsequence'->isLimit {s₁} {s₂} {v} s≤ (f , inc-f , p) lim₂ = record
    { lower = lower
    ; upper = upper
    }
    where
    lower : (q : ℚ) -> Real.L v q -> ∀Largeℕ (\m -> Real.L (s₁ m) q)
    lower q vL-q = ∥-map handle (isLimit.lower lim₂ q vL-q)
      where
      handle : ∀Largeℕ' (\m -> Real.L (s₂ m) q) -> ∀Largeℕ' (\m -> Real.L (s₁ m) q)
      handle (n , L₂) = f n , \m fn≤m -> trans-L-ℝ≤ (L₂ n refl-≤) (trans-=-≤ (sym (p n)) (s≤ fn≤m))

    inf-f : ∀ i -> i ≤ f i
    inf-f zero = zero-≤
    inf-f (suc n) = trans-≤ (suc-≤ (inf-f n)) (inc-f n)

    f-preserves-≤ : ∀ {i j} -> i ≤ j -> f i ≤ f j
    f-preserves-≤ {i} {j} (d , p) = trans-≤-= (rec d) (cong f p)
      where
      rec : ∀ d -> f i ≤ f (d + i)
      rec zero = refl-≤
      rec (suc d) = trans-≤ (rec d) (weaken-< (inc-f (d + i)))

    upper : (q : ℚ) -> Real.U v q -> ∀Largeℕ (\m -> Real.U (s₁ m) q)
    upper q vU-q = ∥-map handle (isLimit.upper lim₂ q vU-q)
      where
      handle : ∀Largeℕ' (\m -> Real.U (s₂ m) q) -> ∀Largeℕ' (\m -> Real.U (s₁ m) q)
      handle (n , U₂) = 0 , \i _ -> bound i
        where
        find-higher : ∀ i -> Σ[ j ∈ ℕ ] (i < f j)
        find-higher i = suc i , inf-f (suc i)

        bound : ∀ i -> Real.U (s₁ i) q
        bound i = trans-ℝ≤-U s-lt U-m
          where
          U-m : Real.U (s₂ (max (suc i) n)) q
          U-m = U₂ (max (suc i) n) max-≤-right

          pm : s₂ (max (suc i) n) == s₁ (f (max (suc i) n))
          pm = sym (p (max (suc i) n))

          i-lt : i ≤ f (max (suc i) n)
          i-lt = weaken-< (trans-≤ (inf-f (suc i)) (f-preserves-≤ max-≤-left))

          s-lt : s₁ i ≤ s₂ (max (suc i) n)
          s-lt = trans-≤-= (s≤ i-lt) (sym pm)


  isNonDecreasing-isLimit-Subsequence->isLimit :
    {s₁ s₂ : Sequence ℝ} {v : ℝ} ->
    (∀ {i₁ i₂ : ℕ} -> i₁ ≤ i₂ -> s₁ i₁ ≤ s₁ i₂) ->
    isSubsequenceOf s₁ s₂ -> isLimit s₂ v -> isLimit s₁ v
  isNonDecreasing-isLimit-Subsequence->isLimit s≤ ss lim₂ =
    unsquash isProp-isLimit (∥-map (\ss -> isNonDecreasing-isLimit-Subsequence'->isLimit s≤ ss lim₂) ss)
