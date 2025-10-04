{-# OPTIONS --cubical --safe --exact-split #-}

module semidomain.instances.rational where

open import apartness.instances.rational
open import heyting-field.instances.rational
open import rational
open import semidomain
open import semidomain.heyting-field

instance
  Semidomain-ℚ : Semidomain Semiring-ℚ isTightApartness-ℚ#
  Semidomain-ℚ = Semidomain-Field
