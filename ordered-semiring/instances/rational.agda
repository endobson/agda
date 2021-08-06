{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.rational where

open import base
open import ordered-semiring
open import order.instances.rational
open import rational
open import rational.order
open import semiring
open import ring.implementations.rational

instance
  LinearlyOrderedSemiringStr-ℚ : LinearlyOrderedSemiringStr RationalSemiring LinearOrderStr-ℚ
  LinearlyOrderedSemiringStr-ℚ = record
    { +₁-preserves-< = r+₁-preserves-order
    ; *-preserves-0< = r*-preserves-0<
    }

  TotallyOrderedSemiringStr-ℚ : TotallyOrderedSemiringStr RationalSemiring TotalOrderStr-ℚ
  TotallyOrderedSemiringStr-ℚ = record
    { +₁-preserves-≤ = r+₁-preserves-≤
    ; *-preserves-0≤ = r*-preserves-0≤
    }
