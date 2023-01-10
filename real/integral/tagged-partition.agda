{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.tagged-partition where

open import base
open import additive-group
open import additive-group.instances.real
open import fin
open import finsum
open import finset.instances
open import order
open import order.instances.nat
open import order.instances.real
open import real
open import real.integral.partition
open import real.integral.partition-index
open import ring.implementations.real
open import semiring

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
