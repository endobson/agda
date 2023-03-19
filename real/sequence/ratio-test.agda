{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.ratio-test where

open import base
open import hlevel
open import real
open import functions
open import order
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import real.sequence.limit
open import real.sequence.absolute-convergence
open import ring.implementations.real
open import semiring
open import sequence
open import relation

private
  Seq : Type₁
  Seq = Sequence ℝ


record isRatioSeq (s1 s2 : Seq) : Type₁ where
  field
    f : ∀ n -> s1 n * s2 n == s1 (suc n)

isProp-isRatioSeq : {s1 s2 : Seq} -> isProp (isRatioSeq s1 s2)
isProp-isRatioSeq {s1} {s2} r1 r2 i .isRatioSeq.f =
  isPropΠ (\n -> isSet-ℝ (s1 n * s2 n) (s1 (suc n))) (isRatioSeq.f r1) (isRatioSeq.f r2) i


ratio-test : {s1 s2 l : Seq} -> isRatioSeq s1 s2 -> isLimit (abs ∘ s2) l -> l < 1#
             isAbsConvergentSeries s1
ratio-test isRatio isLim l<1 = ?
