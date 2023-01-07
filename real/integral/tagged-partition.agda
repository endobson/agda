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
open import ring.implementations.real
open import semiring

record Tagging {a b : ℝ} (p : Partition a b) : Type₁ where
  no-eta-equality
  private
    n = (Partition.n p)
    uℝ = (Partition.uℝ p)

  field
    t-low : ℝ
    t-mid : Fin n -> ℝ
    t-high : ℝ

    a≤t : a ≤ t-low
    t≤u0 : t-low ≤ uℝ zero-fin
    u≤t : (i : Fin n) -> uℝ (inc-fin i) ≤ t-mid i
    t≤u : (i : Fin n) -> t-mid i ≤ uℝ (suc-fin i)
    un≤t : uℝ (n , refl-≤) ≤ t-high
    t≤b : t-high ≤ b

  t : PartitionIndex n -> ℝ
  t pi-low = t-low
  t (pi-mid i) = t-mid i
  t pi-high = t-high

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
  { t-low = a
  ; t-mid = \i -> uℝ (inc-fin i)
  ; t-high = uℝ (n , refl-≤)
  ; a≤t = refl-≤
  ; t≤u0 = weaken-< (Partition.a<u0 p)
  ; u≤t = \i -> refl-≤
  ; t≤u = \i -> weaken-< (Partition.uℝ<uℝ p i)
  ; un≤t = refl-≤
  ; t≤b = weaken-< (Partition.un<b p)
  }
  where
  uℝ = Partition.uℝ p
  n = Partition.n p

right-tagging : {a b : ℝ} -> (p : Partition a b) -> Tagging p
right-tagging {a} {b} p = record
  { t-low = uℝ zero-fin
  ; t-mid = \i -> uℝ (suc-fin i)
  ; t-high = b
  ; a≤t = weaken-< (Partition.a<u0 p)
  ; t≤u0 = refl-≤
  ; u≤t = \i -> weaken-< (Partition.uℝ<uℝ p i)
  ; t≤u = \i -> refl-≤
  ; un≤t = weaken-< (Partition.un<b p)
  ; t≤b = refl-≤
  }
  where
  uℝ = Partition.uℝ p
  n = Partition.n p
