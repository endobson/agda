{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.zero where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import nat
open import order
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import real
open import real.epsilon-bounded
open import real.rational
open import real.sequence.limit
open import sequence

private
  Seq : Type₁
  Seq = Sequence ℝ

opaque
  abs<ε->isLimit0 :
    {seq : Seq} ->
    (((ε , _) : ℚ⁺) -> ∀Largeℕ (\i -> abs (seq i) < ℚ->ℝ ε)) ->
    isLimit seq 0#
  abs<ε->isLimit0 {seq} bound = εBounded-diff->isLimit bound'
    where
    bound' : (((ε , _) : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ε (diff 0# (seq i))))
    bound' ε⁺@(ε , 0<ε) = ∀Largeℕ-map handle (bound ε⁺)
      where
      handle : {i : ℕ} -> abs (seq i) < ℚ->ℝ ε -> εBounded ε (diff 0# (seq i))
      handle {i} as<ε = subst (εBounded ε) path εB
        where
        path : (seq i) == (diff 0# (seq i))
        path = sym diff-step >=> +-left-zero
        εB : εBounded ε (seq i)
        εB = εBounded-abs<ε as<ε
