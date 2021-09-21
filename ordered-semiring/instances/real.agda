{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.real where

open import additive-group.instances.real
open import base
open import ordered-semiring
open import ordered-ring
open import order.instances.real
open import real.arithmetic.order
open import semiring
open import ring.implementations.real

instance
  LinearlyOrderedSemiringStr-ℝ : LinearlyOrderedSemiringStr ℝSemiring LinearOrderStr-ℝ
  LinearlyOrderedSemiringStr-ℝ = record
    { +₁-preserves-< = ℝ+₁-preserves-<
    ; *-preserves-0< = ℝ*-preserves-0<
    }


  PartiallyOrderedSemiringStr-ℝ : PartiallyOrderedSemiringStr ℝSemiring PartialOrderStr-ℝ
  PartiallyOrderedSemiringStr-ℝ = record
    { +₁-preserves-≤ = \a b c -> +₁-preserves-≮ a c b
    ; *-preserves-0≤ = *-preserves-≮0
    }
