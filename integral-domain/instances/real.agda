{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain.instances.real where

open import integral-domain
open import integral-domain.apart-linear-order
open import order.instances.real
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import ring.implementations.real

instance
  IntegralDomain-ℝ : IntegralDomain ℝRing isTightApartness-ℝ#
  IntegralDomain-ℝ = IntegralDomain-LinearOrderStr _ _ 0<1
