{-# OPTIONS --cubical --safe --exact-split #-}

module real.series where

open import additive-group
open import additive-group.instances.reader
open import additive-group.instances.real
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
open import integral-domain.instances.real
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
open import ordered-integral-domain
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.proper-interval
open import real
open import real.arithmetic
open import real.heyting-field
open import real.interval
open import real.order
open import real.rational
open import real.sequence
open import real.sequence.limit
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

isLimit-constant-seq : (x : ℝ) -> isLimit (constant-seq x) x
isLimit-constant-seq x = 
  close->isLimit (\qi x∈qi -> ∣ 0 , (\_ _ -> x∈qi) ∣)

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
