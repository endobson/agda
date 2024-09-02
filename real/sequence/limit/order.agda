{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.order where

open import base
open import heyting-field.instances.real
open import hlevel
open import nat
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import ordered-additive-group.instances.real
open import ordered-field.mean
open import ordered-semiring.instances.real
open import real
open import real.sequence.limit
open import sequence
open import truncation

opaque
  isLimit-preserves-≤ :  {s1 s2 : Sequence ℝ} {l1 l2 : ℝ} ->
    isLimit s1 l1 -> isLimit s2 l2 -> (∀ i -> s1 i ≤ s2 i) -> l1 ≤ l2
  isLimit-preserves-≤ {s1} {s2} {l1} {l2} isLim1 isLim2 s1≤s2 l2<l1 =
    unsquash isPropBot (∥-map2 handle (isLimit.upperℝ isLim2 l2<m) (isLimit.lowerℝ isLim1 m<l1))
    where
    m : ℝ
    m = mean l2 l1
    l2<m : l2 < m
    l2<m = mean-<₁ l2<l1
    m<l1 : m < l1
    m<l1 = mean-<₂ l2<l1

    handle : ∀Largeℕ' (\i -> s2 i < m) -> ∀Largeℕ' (\i -> m < s1 i) -> Bot
    handle (N1 , f1) (N2 , f2) =
      s1≤s2 N (trans-< (f1 N max-≤-left) (f2 N max-≤-right))
      where
      N : ℕ
      N = max N1 N2
