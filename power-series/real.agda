{-# OPTIONS --cubical --safe --exact-split #-}

module power-series.real where

open import power-series
open import real
open import real.series
open import real.series.base
open import real.infinite-sum
open import nat
open import base
open import truncation
open import equivalence.base
open import sequence
open import semiring
open import ring.implementations.real
open import real.series.geometric

eval-power-series : (p : PowerSeries ℝ) -> ℝ -> Sequence ℝ
eval-power-series (power-series s) x n = s n * geometric-sequence x n
