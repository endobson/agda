{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.real where

open import base
open import ordered-semiring
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
