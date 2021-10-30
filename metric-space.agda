{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space where

open import base

private
  variable
    ℓ : Level

-- record MetricSpaceStr (D : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ-zero)) where
--   field
--     distance : D -> D -> ℝ
--     distance-commute : {x y : D} -> distance x y == distance y x
--     distance-triangle : {x y z : D} -> distance x z ≤ (distance x y ℝ+ distance y z)
