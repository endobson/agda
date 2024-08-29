{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.cauchy-product where

open import additive-group.instances.real
open import fin.sum-pair
open import finset.instances.sum-pair
open import finsum
open import real
open import ring.implementations.real
open import semiring
open import sequence

cauchy-product : Sequence ℝ -> Sequence ℝ -> Sequence ℝ
cauchy-product f g n = finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> f i * g j)
