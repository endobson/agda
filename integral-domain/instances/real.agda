{-# OPTIONS --cubical --safe --exact-split #-}

module integral-domain.instances.real where

open import additive-group.instances.real
open import integral-domain
open import integral-domain.apart-linear-order
open import order.instances.real
open import ordered-additive-group.instances.real
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import ring.implementations.real
open import real.rational

instance
  IntegralDomain-ℝ : IntegralDomain ℝRing isTightApartness-ℝ#
  IntegralDomain-ℝ = IntegralDomain-LinearOrderStr _ _ 0ℝ<1ℝ
