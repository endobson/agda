{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.instances.rational where

open import ordered-ring
open import order.instances.rational
open import ordered-semiring.instances.rational
open import ring.implementations.rational

instance
  LinearlyOrderedRingStr-ℚ : LinearlyOrderedRingStr RationalRing LinearOrderStr-ℚ
  LinearlyOrderedRingStr-ℚ = record
    { ordered-semiring = LinearlyOrderedSemiringStr-ℚ
    }
