{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.functions where

open import base
open import real
open import real.series
open import real.trigonometry.taylor-series

sin : ℝ -> ℝ
sin x = fst (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-sin x))

cos : ℝ -> ℝ
cos x = fst (isAbsConvergentSeries->isConvergentSeries (isAbsConvergentSeries-cos x))
