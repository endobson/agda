{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.instances.real where

open import ordered-ring
open import order.instances.real
open import ordered-semiring.instances.real
open import ring.implementations.real

instance
  LinearlyOrderedRingStr-ℝ : LinearlyOrderedRingStr ℝRing LinearOrderStr-ℝ
  LinearlyOrderedRingStr-ℝ = record
    { ordered-semiring = LinearlyOrderedSemiringStr-ℝ
    }
