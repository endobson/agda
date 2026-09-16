{-# OPTIONS --cubical --safe --exact-split #-}

module real.trigonometry.continuous where


open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import real.trigonometry.taylor-series
open import real.trigonometry.functions
open import real
open import nat
open import base
open import functions
open import real.series


-- isContinuous-series-sum :
--   {terms : ℝ -> ℕ -> ℝ} ->
--   (conv : ∀ x -> isConvergentSeries (terms x)) ->
--   isContinuous (\x -> fst (conv x))
-- isContinuous-series-sum {t} conv .isContinuous.at x = ?



-- isContinuous-sin : isContinuous sin
-- isContinuous-sin = ?
