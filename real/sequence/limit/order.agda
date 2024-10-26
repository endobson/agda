{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.order where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import functions
open import funext
open import heyting-field.instances.real
open import hlevel
open import metric-space
open import metric-space.instances.real
open import nat
open import order
open import order.bound
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.bound
open import ordered-additive-group.instances.real
open import ordered-field.mean
open import ordered-semiring.instances.real
open import real
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import sequence
open import subset.subspace
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

opaque
  isNonDecreasing-isSupremum->isLimit : {s : ℕ -> ℝ} {v : ℝ} ->
    (∀ {i j : ℕ} -> i ≤ j -> s i ≤ s j) -> isSupremum s v -> isLimit s v
  isNonDecreasing-isSupremum->isLimit {s} {v} non-dec sup@(v-close , v-above) = distance<ε->isLimit close
    where
    close : ∀ ε -> ∀Largeℕ (\i -> εClose ε v (s i))
    close (ε , 0<ε) = ∥-map handle (v-close v' v'<v)
      where
      v' : ℝ
      v' = diff ε v
      v'<v : v' < v
      v'<v = trans-<-= (+₁-preserves-< (minus-flips-0< 0<ε)) +-right-zero

      d-v'v=ε : diff v' v == ε
      d-v'v=ε = +-right (sym diff-anticommute) >=> diff-step

      handle : Σ[ i ∈ ℕ ] (v' < s i) -> ∀Largeℕ' (\i -> distance v (s i) < ε)
      handle (N , v'<sN) = (N , close2)
        where
        close2 : ∀ i -> N ≤ i -> distance v (s i) < ε
        close2 i N≤i = trans-=-< d=d (trans-<-= d-siv<d-v'v d-v'v=ε)
          where
          v'<si : v' < s i
          v'<si = trans-<-≤ v'<sN (non-dec N≤i)
          si≤v : s i ≤ v
          si≤v = isSupremum->isUpperBound sup i

          d=d : distance v (s i) == diff (s i) v
          d=d = distance-commuteᵉ v (s i) >=> abs-0≤-path (diff-0≤⁺ si≤v)

          d-siv<d-v'v : diff (s i) v < diff v' v
          d-siv<d-v'v = +₁-preserves-< (minus-flips-< v'<si)

  isNonIncreasing-isInfimum->isLimit : {s : ℕ -> ℝ} {v : ℝ} ->
    (∀ {i j : ℕ} -> i ≤ j -> s j ≤ s i) -> isInfimum s v -> isLimit s v
  isNonIncreasing-isInfimum->isLimit {s} {v} non-inc inf =
    subst2 isLimit (funExt (\_ -> minus-double-inverse)) minus-double-inverse
      (minus-preserves-limit (isNonDecreasing-isSupremum->isLimit non-dec sup))
    where
    s' : ℕ -> ℝ
    s' = -_ ∘ s

    non-dec : ∀ {i j : ℕ} -> i ≤ j -> s' i ≤ s' j
    non-dec i≤j = minus-flips-≤ (non-inc i≤j)

    sup : isSupremum s' (- v)
    sup = minus-flips-isInfimum inf
