{-# OPTIONS --cubical --safe --exact-split #-}

module semidomain.instances.real where

open import order.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ring.implementations.real
open import semidomain
open import semidomain.apart-linear-order

instance
  Semidomain-ℝ : Semidomain ℝSemiring isTightApartness-ℝ#
  Semidomain-ℝ = Semidomain-LinearOrderStr 0<1
