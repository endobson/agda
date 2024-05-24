{-# OPTIONS --cubical --safe --exact-split #-}

module real.series where

open import additive-group
open import additive-group.instances.reader
open import additive-group.instances.real
open import additive-group.instances.nat
open import apartness
open import base
open import equality
open import fin
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum
open import finsum.arithmetic
open import functions
open import funext
open import heyting-field
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-additive-group.instances.nat
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.open-interval
open import real.epsilon-bounded
open import real
open import real.arithmetic
open import real.heyting-field
open import real.open-interval
open import real.order
open import real.rational
open import real.sequence
open import real.sequence.cauchy
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import relation
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sequence
open import sequence.partial-sums
open import truncation

open import real.series.base public

private
  Seq : Type₁
  Seq = Sequence ℝ

instance
  AdditiveCommMonoid-Seq : AdditiveCommMonoid Seq
  AdditiveCommMonoid-Seq = AdditiveCommMonoid-Reader AdditiveCommMonoid-ℝ Nat
  AdditiveGroup-Seq : AdditiveGroup AdditiveCommMonoid-Seq
  AdditiveGroup-Seq = AdditiveGroup-Reader AdditiveGroup-ℝ Nat


isInfiniteSum : REL Seq ℝ ℓ-one
isInfiniteSum s r = isLimit (partial-sums s) r

isProp-isInfiniteSum : ∀ {s} {r} -> isProp (isInfiniteSum s r)
isProp-isInfiniteSum = isProp-isLimit

ℝ∈Iℚ-+ᵉ⁻ : (x y : ℝ) (a : Iℚ) -> ℝ∈Iℚ (x ℝ+ᵉ y) a ->
           ∃[ qi1 ∈ Iℚ ] Σ[ qi2 ∈ Iℚ ] (ℝ∈Iℚ x qi1 × ℝ∈Iℚ y qi2 × (qi1 i+ qi2) i⊆ a)
ℝ∈Iℚ-+ᵉ⁻ x y a@(Iℚ-cons l u l≤u) (L-a , U-a) = ∥-map2 handle L-a U-a
  where
  handle : Σ[ l1 ∈ ℚ ] Σ[ l2 ∈ ℚ ] (Real.L x l1 × Real.L y l2 × (l1 + l2) == l) ->
           Σ[ u1 ∈ ℚ ] Σ[ u2 ∈ ℚ ] (Real.U x u1 × Real.U y u2 × (u1 + u2) == u) ->
           Σ[ qi1 ∈ Iℚ ] Σ[ qi2 ∈ Iℚ ] (ℝ∈Iℚ x qi1 × ℝ∈Iℚ y qi2 × (qi1 i+ qi2) i⊆ a)
  handle (l1 , l2 , L-l1 , L-l2 , l1+l2=l) (u1 , u2 , U-u1 , U-u2 , u1+u2=u) =
    (ℝ-bounds->Iℚ x L-l1 U-u1) ,
    (ℝ-bounds->Iℚ y L-l2 U-u2) ,
    (L-l1 , U-u1) ,
    (L-l2 , U-u2) ,
    (i⊆-cons (subst2 _≤_ l1+l2=l refl refl-≤) (subst2 _≤_ refl u1+u2=u refl-≤))

ℝ∈Iℚ-+⁻ : (x y : ℝ) (a : Iℚ) -> ℝ∈Iℚ (x + y) a ->
          ∃[ qi1 ∈ Iℚ ] Σ[ qi2 ∈ Iℚ ] (ℝ∈Iℚ x qi1 × ℝ∈Iℚ y qi2 × (qi1 i+ qi2) i⊆ a)
ℝ∈Iℚ-+⁻ x y a x+y∈a =
  ℝ∈Iℚ-+ᵉ⁻ x y a (subst (\z -> ℝ∈Iℚ z a) ℝ+-eval x+y∈a)


isLimit-seq-cons : (x : ℝ) (s : Seq) (v : ℝ) -> isLimit s v -> isLimit (seq-cons x s) v
isLimit-seq-cons x s v l = close->isLimit f
  where
  f : (qi : Iℚ) -> (ℝ∈Iℚ v qi) -> ∃[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (seq-cons x s m) qi)
  f qi v∈qi = ∥-map handle (isLimit.close l qi v∈qi)
    where
    handle : Σ[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (s m) qi) ->
             Σ[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (seq-cons x s m) qi)
    handle (n , g) = suc n , h
      where
      h : (m : ℕ) -> m ≥ (suc n) -> ℝ∈Iℚ (seq-cons x s m) qi
      h zero sn≤z = bot-elim (zero-≮ sn≤z)
      h (suc m) sn≤sm = g m (pred-≤ sn≤sm)

isConvergentSeries->zero-limit : {s : Seq} -> isConvergentSeries s -> isLimit s 0#
isConvergentSeries->zero-limit {s} (l , lim-partial) =
  subst2 isLimit (funExt diff-path) +-inverse lim-diff
  where
  lim-diff : isLimit (diff (partial-sums s) (dropN 1 (partial-sums s))) (diff l l)
  lim-diff = diff-preserves-limit lim-partial (dropN-preserves-limit lim-partial)

  diff-path : ∀ n -> (diff (partial-sums s n) (dropN 1 (partial-sums s) n)) == s n
  diff-path n = cong (diff (partial-sums s n)) (partial-sums-split s n) >=>
                +-assoc >=> +-right +-inverse >=> +-right-zero

-- TODO add isConvergentSequence-const
isConvergentSeries-zero-seq : isConvergentSeries (\_ -> 0#)
isConvergentSeries-zero-seq =
  subst isConvergentSequence (funExt (\n -> sym (finiteMerge-ε _ (\_ -> refl))))
    (0# , isLimit-constant-seq 0#)


squeeze-isConvergentSeries :
  {s1 s2 s3 : Seq} ->
  (∀Largeℕ (\ m -> s1 m ≤ s2 m)) ->
  (∀Largeℕ (\ m -> s2 m ≤ s3 m)) ->
  isConvergentSeries s1 ->
  isConvergentSeries s3 ->
  isConvergentSeries s2
squeeze-isConvergentSeries {s1} {s2} {s3} ∀s1≤s2 ∀s2≤s3 (l1 , lim-part1) (l3 , lim-part3) =
  isCauchy->isConvergentSequence (oneSidedCauchy->isCauchy cauchy)
  where
  cauchy1 : isCauchy (partial-sums s1)
  cauchy1 = isConvergentSequence->isCauchy (l1 , lim-part1)
  cauchy3 : isCauchy (partial-sums s3)
  cauchy3 = isConvergentSequence->isCauchy (l3 , lim-part3)

  cauchy : (ε : ℚ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> m₁ ≤ m₂ ->
                                     εBounded ⟨ ε ⟩ (diff (partial-sums s2 m₁) (partial-sums s2 m₂)))
  cauchy ε⁺@(ε , _) = ∥-map4 handle (cauchy1 ε⁺) (cauchy3 ε⁺) ∀s1≤s2 ∀s2≤s3
    where
    handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                           εBounded ε (diff (partial-sums s1 m₁) (partial-sums s1 m₂))) ->
             Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                           εBounded ε (diff (partial-sums s3 m₁) (partial-sums s3 m₂))) ->
             ∀Largeℕ' (\m -> s1 m ≤ s2 m) ->
             ∀Largeℕ' (\m -> s2 m ≤ s3 m) ->
             Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> m₁ ≤ m₂ ->
                           εBounded ε (diff (partial-sums s2 m₁) (partial-sums s2 m₂)))
    handle (n1 , f1) (n3 , f3) (n12 , f12) (n23 , f23) = max (max n1 n3) (max n12 n23) , g
      where
      g : (m₁ m₂ : Nat) -> max (max n1 n3) (max n12 n23) ≤ m₁ -> m₁ ≤ m₂ ->
          εBounded ε (diff (partial-sums s2 m₁) (partial-sums s2 m₂))
      g m₁ m₂ max≤m₁ m₁≤m₂@(i , _) =
        subst (εBounded ε) (sym (diff-partial-sums s2 m₁ m₂ m₁≤m₂)) (lower , upper)
        where
        n1≤m₁ = trans-≤ max-≤-left (trans-≤ max-≤-left max≤m₁)
        n3≤m₁ = trans-≤ max-≤-right (trans-≤ max-≤-left max≤m₁)
        n12≤m₁ = trans-≤ max-≤-left (trans-≤ max-≤-right max≤m₁)
        n23≤m₁ = trans-≤ max-≤-right (trans-≤ max-≤-right max≤m₁)
        p1 : (partial-sums (dropN m₁ s1) i) ≤ (partial-sums (dropN m₁ s2) i)
        p1 = partial-sums-≤ (\n -> f12 (m₁ + n) (trans-=-≤ (sym +-right-zero)
                                                           (+-preserves-≤ n12≤m₁ zero-≤))) i
        p3 : (partial-sums (dropN m₁ s2) i) ≤ (partial-sums (dropN m₁ s3) i)
        p3 = partial-sums-≤ (\n -> f23 (m₁ + n) (trans-=-≤ (sym +-right-zero)
                                                           (+-preserves-≤ n23≤m₁ zero-≤))) i

        lower : Real.L (partial-sums (dropN m₁ s2) i) (r- ε)
        lower = trans-L-ℝ≤ (proj₁ (f1 m₁ m₂ n1≤m₁ (trans-≤ n1≤m₁ m₁≤m₂)))
                           (trans-=-≤ (diff-partial-sums s1 m₁ m₂ m₁≤m₂) p1)
        upper : Real.U (partial-sums (dropN m₁ s2) i) ε
        upper = trans-ℝ≤-U (trans-≤-= p3 (sym (diff-partial-sums s3 m₁ m₂ m₁≤m₂)))
                           (proj₂ (f3 m₁ m₂ n3≤m₁ (trans-≤ n3≤m₁ m₁≤m₂)))
