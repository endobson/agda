{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.minmax where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import functions
open import metric-space
open import metric-space.instances.real
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-additive-group.minmax
open import real
open import real.distance
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.subspace
open import sequence
open import subset.subspace
open import truncation

private
  dis<ε->diff-max<ε : {a b c d : ℝ} {ε : ℝ} (ab<ε : distance a b < ε) (cd<ε : distance c d < ε) ->
                      diff (max a c) (max b d) < ε
  dis<ε->diff-max<ε {a} {b} {c} {d} {ε} ab<ε cd<ε = lt6
    where
    dab<ε : diff a b < ε
    dab<ε = trans-≤-< max-≤-left ab<ε
    dcd<ε : diff c d < ε
    dcd<ε = trans-≤-< max-≤-left cd<ε
    lt1 : diff (max a c) b ≤ diff a b
    lt1 = +₁-preserves-≤ (minus-flips-≤ max-≤-left)
    lt2 : diff (max a c) b < ε
    lt2 = trans-≤-< lt1 dab<ε
    lt3 : diff (max a c) d ≤ diff c d
    lt3 = +₁-preserves-≤ (minus-flips-≤ max-≤-right)
    lt4 : diff (max a c) d < ε
    lt4 = trans-≤-< (+₁-preserves-≤ (minus-flips-≤ max-≤-right))
                    dcd<ε
    lt5 : max (diff (max a c) b) (diff (max a c) d) < ε
    lt5 = max-least-< lt2 lt4
    lt6 : diff (max a c) (max b d) < ε
    lt6 = trans-=-< +-distrib-max-right lt5

  dis<ε->diff-max<ε' : {a b c d : ℝ} {ε : ℝ} (ab<ε : distance a b < ε) (cd<ε : distance c d < ε) ->
                       diff (max b d) (max a c) < ε
  dis<ε->diff-max<ε' ab<ε cd<ε =
    dis<ε->diff-max<ε (trans-=-< distance-commute ab<ε) (trans-=-< distance-commute cd<ε)

  dis<ε->distance-max<ε : {a b c d : ℝ} {ε : ℝ} (ab<ε : distance a b < ε) (cd<ε : distance c d < ε) ->
                         distance (max a c) (max b d) < ε
  dis<ε->distance-max<ε ab<ε cd<ε =
    max-least-< (dis<ε->diff-max<ε ab<ε cd<ε)
                (trans-=-< (sym diff-anticommute) (dis<ε->diff-max<ε' ab<ε cd<ε))

  dis<ε->distance-min<ε : {a b c d : ℝ} {ε : ℝ} (ab<ε : distance a b < ε) (cd<ε : distance c d < ε) ->
                         distance (min a c) (min b d) < ε
  dis<ε->distance-min<ε {a} {b} {c} {d} {ε} ab<ε cd<ε =
    trans-=-< p4 (dis<ε->distance-max<ε (trans-=-< (sym minus-preserves-distance) ab<ε)
                                        (trans-=-< (sym minus-preserves-distance) cd<ε))
    where
    p1 : min a c == - max (- a) (- c)
    p1 = cong2 min (sym minus-double-inverse) (sym minus-double-inverse) >=>
         sym minus-max-path
    p2 : min b d == - max (- b) (- d)
    p2 = cong2 min (sym minus-double-inverse) (sym minus-double-inverse) >=>
         sym minus-max-path
    p3 : diff (min a c) (min b d) ==
         diff (max (- b) (- d)) (max (- a) (- c))
    p3 = cong2 diff p1 p2 >=>
         sym minus-distrib-plus >=>
         sym diff-anticommute

    p4 : distance (min a c) (min b d) ==
         distance (max (- a) (- c)) (max (- b) (- d))
    p4 = cong2 distance p1 p2 >=> sym minus-preserves-distance


opaque
  max-preserves-limit :
    {s1 s2 : Sequence ℝ} -> {v1 v2 : ℝ} ->
    isLimit s1 v1 -> isLimit s2 v2 -> isLimit (\i -> max (s1 i) (s2 i)) (max v1 v2)
  max-preserves-limit {s1} {s2} {v1} {v2} lim1 lim2 =
    distance<ε->isLimit (\ε ->
      (∥-map2 (handle ε) (isLimit.distance<ε lim1 ε) (isLimit.distance<ε lim2 ε)))
    where
    handle : ((ε , _) : ℝ⁺) ->
      ∀Largeℕ' (\i -> (abs (diff v1 (s1 i))) < ε) ->
      ∀Largeℕ' (\i -> (abs (diff v2 (s2 i))) < ε) ->
      ∀Largeℕ' (\i -> (abs (diff (max v1 v2) (max (s1 i) (s2 i)))) < ε)
    handle (ε , _) (N1 , b1) (N2 , b2) = max N1 N2 , bound
      where
      bound : ∀ i -> max N1 N2 ≤ i -> (abs (diff (max v1 v2) (max (s1 i) (s2 i)))) < ε
      bound i Ns≤i =
        dis<ε->distance-max<ε (b1 i (trans-≤ max-≤-left Ns≤i))
                              (b2 i (trans-≤ max-≤-right Ns≤i))

  min-preserves-limit :
    {s1 s2 : Sequence ℝ} -> {v1 v2 : ℝ} ->
    isLimit s1 v1 -> isLimit s2 v2 -> isLimit (\i -> min (s1 i) (s2 i)) (min v1 v2)
  min-preserves-limit {s1} {s2} {v1} {v2} lim1 lim2 =
    distance<ε->isLimit (\ε ->
      (∥-map2 (handle ε) (isLimit.distance<ε lim1 ε) (isLimit.distance<ε lim2 ε)))
    where
    handle : ((ε , _) : ℝ⁺) ->
      ∀Largeℕ' (\i -> (abs (diff v1 (s1 i))) < ε) ->
      ∀Largeℕ' (\i -> (abs (diff v2 (s2 i))) < ε) ->
      ∀Largeℕ' (\i -> (abs (diff (min v1 v2) (min (s1 i) (s2 i)))) < ε)
    handle (ε , _) (N1 , b1) (N2 , b2) = max N1 N2 , bound
      where
      bound : ∀ i -> max N1 N2 ≤ i -> (abs (diff (min v1 v2) (min (s1 i) (s2 i)))) < ε
      bound i Ns≤i =
        dis<ε->distance-min<ε (b1 i (trans-≤ max-≤-left Ns≤i))
                              (b2 i (trans-≤ max-≤-right Ns≤i))

  abs-preserves-limit : {s : Sequence ℝ} -> {v : ℝ} -> isLimit s v -> isLimit (abs ∘ s) (abs v)
  abs-preserves-limit lim = max-preserves-limit lim (minus-preserves-limit lim)
