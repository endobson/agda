{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.tagged-partition where

open import base
open import additive-group
open import additive-group.instances.real
open import fin
open import finsum
open import finset.instances
open import order
open import order.instances.real
open import real
open import real.integral.partition
open import ring.implementations.real
open import semiring

record Tagging {a b : ℝ} (p : Partition a b) : Type₁ where
  no-eta-equality
  private
    n = (Partition.n p)
    u = (Partition.u p)

  field
    t : Fin n -> ℝ
    u≤t : (i : Fin n) -> u (inc-fin i) ≤ t i
    t≤u : (i : Fin n) -> t i ≤ u (suc-fin i)

TaggedPartition : ℝ -> ℝ -> Type₁
TaggedPartition a b = Σ (Partition a b) Tagging

riemann-sum : {a b : ℝ} -> (f : ℝ -> ℝ) -> TaggedPartition a b -> ℝ
riemann-sum f (p , t) =
  finiteSum (\ (i : Fin p.n) -> f (t.t i) * p.width i)
  where
  module p = Partition p
  module t = Tagging t


left-tagging : {a b : ℝ} -> (p : Partition a b) -> Tagging p
left-tagging p = record
  { t = \i -> Partition.u p (inc-fin i)
  ; u≤t = \i -> refl-≤
  ; t≤u = \i -> Partition.u≤u p i
  }

right-tagging : {a b : ℝ} -> (p : Partition a b) -> Tagging p
right-tagging p = record
  { t = \i -> Partition.u p (suc-fin i)
  ; u≤t = \i -> Partition.u≤u p i
  ; t≤u = \i -> refl-≤
  }
