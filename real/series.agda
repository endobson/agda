{-# OPTIONS --cubical --safe --exact-split #-}

module real.series where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum.arithmetic
open import functions
open import funext
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import rational
open import real
open import real.epsilon-bounded
open import real.order
open import real.sequence.cauchy
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import sequence
open import sequence.partial-sums
open import truncation

open import real.series.base public

opaque
  isConvergentSeries-zero-seq : isConvergentSeries (\_ -> 0#)
  isConvergentSeries-zero-seq =
    subst isConvergentSequence (funExt (\n -> sym (finiteMerge-ε _ (\_ -> refl))))
      (0# , isLimit-constant-seq 0#)

  isConvergentSeries-minus : {s : Sequence ℝ} -> isConvergentSeries s ->
                             isConvergentSeries (\i -> - (s i))
  isConvergentSeries-minus (l , isLim) =
    - l , subst (\s -> isLimit s (- l)) (funExt (\n -> (sym finiteSum--)))
                (minus-preserves-limit isLim)

opaque
  isConvergentSeries->zero-limit : {s : Sequence ℝ} -> isConvergentSeries s -> isLimit s 0#
  isConvergentSeries->zero-limit {s} (l , lim-partial) =
    subst2 isLimit (funExt diff-path) +-inverse lim-diff
    where
    lim-diff : isLimit (\n -> (diff (partial-sums s n) (partial-sums s (suc n)))) (diff l l)
    lim-diff = diff-preserves-limit lim-partial (dropN-preserves-limit lim-partial)


    diff-path : ∀ n -> (diff (partial-sums s n) (dropN 1 (partial-sums s) n)) == s n
    diff-path n = cong (diff (partial-sums s n)) (partial-sums-split s n) >=>
                  +-assoc >=> +-right +-inverse >=> +-right-zero


opaque
  dropN-preserves-isConvergentSeries : {s : Sequence ℝ} {n : Nat} ->
    isConvergentSeries s -> isConvergentSeries (dropN n s)
  dropN-preserves-isConvergentSeries {s} {n} (l , isLim-l) = (_ , isLim-drop)
    where
    isLim-drop : isLimit (partial-sums (dropN n s)) (diff (partial-sums s n) l)
    isLim-drop =
      subst2 isLimit (funExt p2) refl
        (diff-preserves-limit
          (isLimit-constant-seq (partial-sums s n))
          (dropN-preserves-limit isLim-l))
      where
      p2 : ∀ m -> (diff (partial-sums s n) (dropN n (partial-sums s) m)) == (partial-sums (dropN n s) m)
      p2 m =
        +-left (sym (partial-sums-dropN s n m)) >=>
        +-left +-commute >=> +-assoc >=> +-right +-inverse >=> +-right-zero

  dropN-reflects-isConvergentSeries : {s : Sequence ℝ} {n : Nat} ->
    isConvergentSeries (dropN n s) -> isConvergentSeries s
  dropN-reflects-isConvergentSeries {s} {n} (l , isLim-l) = (_ , isLim-undrop)
    where
    isLim-undrop : isLimit (partial-sums s) (partial-sums s n + l)
    isLim-undrop =
      dropN-reflects-limit
        (subst2 isLimit (funExt (\i -> partial-sums-dropN s n i)) refl
          (+-preserves-limit (isLimit-constant-seq (partial-sums s n)) isLim-l))

opaque
  squeeze-isConvergentSeries :
    {s1 s2 s3 : Sequence ℝ} ->
    (∀Largeℕ (\ m -> s1 m ≤ s2 m)) ->
    (∀Largeℕ (\ m -> s2 m ≤ s3 m)) ->
    isConvergentSeries s1 ->
    isConvergentSeries s3 ->
    isConvergentSeries s2
  squeeze-isConvergentSeries {s1} {s2} {s3} ∀s1≤s2 ∀s2≤s3 (l1 , lim-part1) (l3 , lim-part3) =
    isCauchy->isConvergentSequence (isCauchy'->isCauchy cauchy)
    where
    cauchy1 : isCauchy (partial-sums s1)
    cauchy1 = isConvergentSequence->isCauchy (l1 , lim-part1)
    cauchy3 : isCauchy (partial-sums s3)
    cauchy3 = isConvergentSequence->isCauchy (l3 , lim-part3)

    cauchy : isCauchy' (partial-sums s2)
    cauchy ε⁺@(ε , _) = ∥-map4 handle (cauchy1 ε⁺) (cauchy3 ε⁺) ∀s1≤s2 ∀s2≤s3
      where
      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                             εBounded ε (diff (partial-sums s1 m₁) (partial-sums s1 m₂))) ->
               Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                             εBounded ε (diff (partial-sums s3 m₁) (partial-sums s3 m₂))) ->
               ∀Largeℕ' (\m -> s1 m ≤ s2 m) ->
               ∀Largeℕ' (\m -> s2 m ≤ s3 m) ->
               ∀Largeℕ' (\m₁ -> (m₂ : Nat) -> m₁ ≤ m₂ ->
                                εBounded ε (diff (partial-sums s2 m₁) (partial-sums s2 m₂)))
      handle (n1 , f1) (n3 , f3) (n12 , f12) (n23 , f23) = max (max n1 n3) (max n12 n23) , g
        where
        g : (m₁ : Nat) -> max (max n1 n3) (max n12 n23) ≤ m₁ -> (m₂ : Nat) -> m₁ ≤ m₂ ->
            εBounded ε (diff (partial-sums s2 m₁) (partial-sums s2 m₂))
        g m₁ max≤m₁ m₂ m₁≤m₂@(i , _) =
          subst (εBounded ε) (sym (diff-partial-sums s2 m₁ m₂ m₁≤m₂)) (lower , upper)
          where
          n1≤m₁ : n1 ≤ m₁
          n1≤m₁ = trans-≤ max-≤-left (trans-≤ max-≤-left max≤m₁)
          n3≤m₁ : n3 ≤ m₁
          n3≤m₁ = trans-≤ max-≤-right (trans-≤ max-≤-left max≤m₁)
          n12≤m₁ : n12 ≤ m₁
          n12≤m₁ = trans-≤ max-≤-left (trans-≤ max-≤-right max≤m₁)
          n23≤m₁ : n23 ≤ m₁
          n23≤m₁ = trans-≤ max-≤-right (trans-≤ max-≤-right max≤m₁)
          p1 : (partial-sums (dropN m₁ s1) i) ≤ (partial-sums (dropN m₁ s2) i)
          p1 = partial-sums-≤ (\n -> f12 (m₁ + n) (trans-=-≤ (sym +-right-zero)
                                                             (+-preserves-≤ n12≤m₁ zero-≤))) i
          p3 : (partial-sums (dropN m₁ s2) i) ≤ (partial-sums (dropN m₁ s3) i)
          p3 = partial-sums-≤ (\n -> f23 (m₁ + n) (trans-=-≤ (sym +-right-zero)
                                                             (+-preserves-≤ n23≤m₁ zero-≤))) i

          lower : Real.L (partial-sums (dropN m₁ s2) i) (- ε)
          lower = trans-L-ℝ≤ (proj₁ (f1 m₁ m₂ n1≤m₁ (trans-≤ n1≤m₁ m₁≤m₂)))
                             (trans-=-≤ (diff-partial-sums s1 m₁ m₂ m₁≤m₂) p1)
          upper : Real.U (partial-sums (dropN m₁ s2) i) ε
          upper = trans-ℝ≤-U (trans-≤-= p3 (sym (diff-partial-sums s3 m₁ m₂ m₁≤m₂)))
                             (proj₂ (f3 m₁ m₂ n3≤m₁ (trans-≤ n3≤m₁ m₁≤m₂)))

opaque
  squeeze-abs-isConvergentSeries :
    {s1 s2 : Sequence ℝ} ->
    (∀Largeℕ (\ m -> abs (s1 m) ≤ s2 m)) ->
    isConvergentSeries s2 ->
    isConvergentSeries s1
  squeeze-abs-isConvergentSeries {s1} {s2} as1≤s2 conv-s2@(l2 , isLim-s2) =
    squeeze-isConvergentSeries
      -s2≤s1
      s1≤s2
      (- l2 , isLim-ms2)
      conv-s2

    where
    s1≤s2 : ∀Largeℕ (\ m -> s1 m ≤ s2 m)
    s1≤s2 = ∀Largeℕ-map (\as1≤s2 -> trans-≤ abs-≤ as1≤s2) as1≤s2

    -s2≤s1 : ∀Largeℕ (\ m -> (- s2 m) ≤ s1 m)
    -s2≤s1 =
      ∀Largeℕ-map
        (\as1≤s2 -> trans-≤-= (minus-flips-≤ (trans-≤ max-≤-right as1≤s2)) minus-double-inverse)
        as1≤s2

    isLim-ms2 : isLimit (partial-sums (-_ ∘ s2)) (- l2)
    isLim-ms2 = subst2 isLimit (funExt (\_ -> (sym finiteSum--))) refl
                  (minus-preserves-limit isLim-s2)

opaque
  squeeze-isAbsConvergentSeries :
    {s1 s2 : Sequence ℝ} ->
    (∀Largeℕ (\ m -> abs (s1 m) ≤ abs (s2 m))) ->
    isAbsConvergentSeries s2 ->
    isAbsConvergentSeries s1
  squeeze-isAbsConvergentSeries {s1} {s2} large conv =
    squeeze-isConvergentSeries lower large (isConvergentSeries-minus conv) conv
    where
    lower : ∀Largeℕ (\m -> (- (abs (s2 m))) ≤ abs (s1 m))
    lower = ∀Largeℕ-map (\lt -> trans-≤ (minus-flips-0≤ abs-0≤) abs-0≤) large


opaque
  isAbsConvergentSeries->isConvergentSeries :
    {s : Sequence ℝ} -> isAbsConvergentSeries s -> isConvergentSeries s
  isAbsConvergentSeries->isConvergentSeries {s} abs-conv@(l , isLim) =
    squeeze-isConvergentSeries
      (∣( 0 , \_ _ -> trans-≤-= (minus-flips-≤ max-≤-right) minus-double-inverse )∣)
      (∣( 0 , \_ _ -> max-≤-left )∣)
      (isConvergentSeries-minus abs-conv) abs-conv
