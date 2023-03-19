{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.base where

open import additive-group.instances.real
open import base
open import functions
open import hlevel
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import real
open import real.sequence.limit
open import relation
open import sequence
open import sequence.partial-sums

private
  Seq : Type₁
  Seq = Sequence ℝ

isConvergentSeries : Pred Seq ℓ-one
isConvergentSeries s = isConvergentSequence (partial-sums s)

isAbsConvergentSeries : Pred Seq ℓ-one
isAbsConvergentSeries s = isConvergentSeries (abs ∘ s)

isProp-isConvergentSeries : {s : Seq} -> isProp (isConvergentSeries s)
isProp-isConvergentSeries = isProp-isConvergentSequence
