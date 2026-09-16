{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.functions where

open import additive-group.instances.real
open import base
open import real
open import real.sequence.limit
open import real.series
open import real.trigonometry.taylor-series
open import sequence.partial-sums

sin : ℝ -> ℝ
sin x = fst (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-sin x))

cos : ℝ -> ℝ
cos x = fst (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-cos x))

isLimit-sin-terms : ∀ x -> isLimit (partial-sums (sin-terms x)) (sin x)
isLimit-sin-terms x = snd (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-sin x))

isLimit-cos-terms : ∀ x -> isLimit (partial-sums (cos-terms x)) (cos x)
isLimit-cos-terms x = snd (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-cos x))
