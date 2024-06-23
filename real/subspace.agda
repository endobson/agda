{-# OPTIONS --cubical --safe --exact-split #-}

module real.subspace where

open import additive-group
open import additive-group.instances.real
open import base
open import order
open import order.instances.real
open import real
open import subset
open import subset.subspace

ℝ⁺S : Subtype ℝ ℓ-one
ℝ⁺S x = 0# < x , isProp-<

ℝ⁺ : Type₁
ℝ⁺ = Subspace ℝ⁺S
