{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.zero where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import funext
open import metric-space
open import metric-space.instances.real
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import real
open import real.sequence.limit
open import real.subspace
open import sequence
open import subset.subspace

opaque
  abs<ε->isLimit0 :
    {seq : Sequence ℝ} ->
    (((ε , _) : ℝ⁺) -> ∀Largeℕ (\i -> abs (seq i) < ε)) ->
    isLimit seq 0#
  abs<ε->isLimit0 {seq} bound = distance<ε->isLimit bound'
    where
    bound' : ((ε , _) : ℝ⁺) -> ∀Largeℕ (\i -> distance 0# (seq i) < ε)
    bound' = transport (\j -> ((ε , _) : ℝ⁺) -> ∀Largeℕ (\i -> abs (p i j) < ε)) bound
      where
      p : ∀ i -> (seq i) == diff 0# (seq i)
      p i = sym diff0-path

  isLimit0->abs<ε :
    {seq : Sequence ℝ} -> isLimit seq 0# -> ((ε , _) : ℝ⁺) ->
    ∀Largeℕ (\i -> abs (seq i) < ε)
  isLimit0->abs<ε {seq} isLim ε⁺@(ε , _) =
    subst ∀Largeℕ (funExt (\i -> cong (_< ε) (cong abs (sym +-left-zero >=> diff-step))))
      (isLimit.distance<ε isLim ε⁺)
