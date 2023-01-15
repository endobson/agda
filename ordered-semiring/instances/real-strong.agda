{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.instances.real-strong where

open import integral-domain.instances.real
open import order.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.integral-domain
open import real.heyting-field
open import real.order
open import ring.implementations.real

instance
  StronglyLinearlyOrderedSemiringStr-ℝ : StronglyLinearlyOrderedSemiringStr ℝSemiring LinearOrderStr-ℝ
  StronglyLinearlyOrderedSemiringStr-ℝ = StronglyLinearlyOrderedSemiringStr-IntegralDomain
