{-# OPTIONS --cubical --safe --exact-split #-}

module power-series.real where

open import power-series
open import real
open import real.series.geometric
open import ring.implementations.real
open import semiring
open import sequence

eval-power-series : (p : PowerSeries ℝ) -> ℝ -> Sequence ℝ
eval-power-series (power-series s) x n = s n * geometric-sequence x n
