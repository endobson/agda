{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.tagged-partition where

open import base
open import additive-group
open import additive-group.instances.real
open import fin
open import equality
open import finsum
open import functions
open import finset.instances
open import finset
open import finsum.arithmetic
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import order
open import order.instances.nat
open import order.instances.real
open import real
open import relation
open import real.integral.partition
open import real.integral.partition-index
open import ring.implementations.real
open import semiring

open EqReasoning

record Tagging {a b : ℝ} (p : Partition a b) : Type₁ where
  no-eta-equality
  private
    n = (Partition.n p)
    uB = (Partition.uB p)

  field
    t : PartitionIndex n -> ℝ
    t∈bounds : (i : PartitionIndex n) -> (uB ⟨ index->low-boundary i ⟩ ≤ t i ×
                                          t i ≤ uB ⟨ index->high-boundary i ⟩)

TaggedPartition : ℝ -> ℝ -> Type₁
TaggedPartition a b = Σ (Partition a b) Tagging

riemann-sum : {a b : ℝ} -> (f : ℝ -> ℝ) -> TaggedPartition a b -> ℝ
riemann-sum f (p , t) =
  finiteSum (\ (i : PartitionIndex p.n) -> f (t.t i) * p.width i)
  where
  module p = Partition p
  module t = Tagging t


left-tagging : {a b : ℝ} -> (p : Partition a b) -> Tagging p
left-tagging {a} {b} p = record
  { t = t
  ; t∈bounds = t∈bounds
  }
  where
  uℝ = Partition.uℝ p
  uB = Partition.uB p
  n = Partition.n p

  t : PartitionIndex n -> ℝ
  t pi-low = a
  t (pi-mid i) = uℝ (inc-fin i)
  t pi-high = uℝ (n , refl-≤)
  t∈bounds : (i : PartitionIndex n) -> (uB ⟨ index->low-boundary i ⟩ ≤ t i ×
                                        t i ≤ uB ⟨ index->high-boundary i ⟩)
  t∈bounds pi-low = refl-≤ , weaken-< (Partition.a<u0 p)
  t∈bounds (pi-mid i) = refl-≤ , weaken-< (Partition.uℝ<uℝ p i)
  t∈bounds pi-high = refl-≤ , weaken-< (Partition.un<b p)

right-tagging : {a b : ℝ} -> (p : Partition a b) -> Tagging p
right-tagging {a} {b} p = record
  { t = t
  ; t∈bounds = t∈bounds
  }
  where
  uℝ = Partition.uℝ p
  uB = Partition.uB p
  n = Partition.n p

  t : PartitionIndex n -> ℝ
  t pi-low = uℝ zero-fin
  t (pi-mid i) = uℝ (suc-fin i)
  t pi-high = b
  t∈bounds : (i : PartitionIndex n) -> (uB ⟨ index->low-boundary i ⟩ ≤ t i ×
                                        t i ≤ uB ⟨ index->high-boundary i ⟩)
  t∈bounds pi-low = weaken-< (Partition.a<u0 p) , refl-≤
  t∈bounds (pi-mid i) = weaken-< (Partition.uℝ<uℝ p i) , refl-≤
  t∈bounds pi-high = weaken-< (Partition.un<b p) , refl-≤


module _ {a b : ℝ} (p : Partition a b) where
  private
    module p = Partition p

    module _ (f : PartitionBoundary p.n -> ℝ) where
      private
        fl : Σ (PartitionBoundary p.n) LowPartitionBoundary -> ℝ
        fl (b , _) = f b

        f¬l : Σ (PartitionBoundary p.n) (Comp LowPartitionBoundary) -> ℝ
        f¬l (b , _) = f b

        fl-i : PartitionIndex p.n -> ℝ
        fl-i = fl ∘ index->low-boundary

        fh : Σ (PartitionBoundary p.n) HighPartitionBoundary -> ℝ
        fh (b , _) = f b

        f¬h : Σ (PartitionBoundary p.n) (Comp HighPartitionBoundary) -> ℝ
        f¬h (b , _) = f b

        fh-i : PartitionIndex p.n -> ℝ
        fh-i = fh ∘ index->high-boundary

      low-sum : finiteSum fl-i == finiteSum fl
      low-sum = sym (finiteMerge-convert _ (index->low-boundary-eq) fl)

      high-sum : finiteSum fh-i == finiteSum fh
      high-sum = sym (finiteMerge-convert _ (index->high-boundary-eq) fh)

      split-sum-low : finiteSum f == finiteSum fl + finiteSum f¬l
      split-sum-low =
        finiteMerge-Detachable _
          (\pb -> LowPartitionBoundary pb , isProp-LowPartitionBoundary pb)
          Decidable-LowPartitionBoundary
          f

      split-sum-high : finiteSum f == finiteSum fh + finiteSum f¬h
      split-sum-high =
        finiteMerge-Detachable _
          (\pb -> HighPartitionBoundary pb , isProp-HighPartitionBoundary pb)
          Decidable-HighPartitionBoundary
          f

      ¬low-sum : finiteSum f¬l == f pb-high
      ¬low-sum = finiteMerge-isContr _ isContr-Σ¬LowPartitionBoundary f¬l

      ¬high-sum : finiteSum f¬h == f pb-low
      ¬high-sum = finiteMerge-isContr _ isContr-Σ¬HighPartitionBoundary f¬h

      split-sum-low' : finiteSum fl-i == diff (f pb-high) (finiteSum f)
      split-sum-low' =
        low-sum >=>
        sym +-right-zero >=>
        +-right (sym +-inverse) >=>
        sym +-assoc >=>
        cong2 diff ¬low-sum (sym split-sum-low)

      split-sum-high' : finiteSum fh-i == diff (f pb-low) (finiteSum f)
      split-sum-high' =
        high-sum >=>
        sym +-right-zero >=>
        +-right (sym +-inverse) >=>
        sym +-assoc >=>
        cong2 diff ¬high-sum (sym split-sum-high)

  sum-width : finiteSum p.width == (diff a b)
  sum-width =
    begin
      finiteSum p.width
    ==< finiteMerge-split _ >
      finiteSum p.interval-high + finiteSum (\x -> - (p.interval-low x))
    ==< +-right finiteSum-- >
      finiteSum p.interval-high + - finiteSum p.interval-low
    ==<>
      diff (finiteSum p.interval-low) (finiteSum p.interval-high)
    ==< cong2 diff (split-sum-low' p.uB) (split-sum-high' p.uB) >
      diff (diff b (finiteSum p.uB)) (diff a (finiteSum p.uB))
    ==< +-right (sym diff-anticommute) >
      (diff a (finiteSum p.uB)) + (diff (finiteSum p.uB) b)
    ==< diff-trans >
      (diff a b)
    end
