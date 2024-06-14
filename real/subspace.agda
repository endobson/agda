{-# OPTIONS --cubical --safe --exact-split #-}

module real.subspace where

open import apartness
open import additive-group
open import additive-group.instances.real
open import base
open import order
open import order.instances.real
open import real
open import subset
open import subset.subspace
open import truncation

ℝ⁺S : Subtype ℝ ℓ-one
ℝ⁺S x = 0# < x , isProp-<

ℝ⁺ : Type₁
ℝ⁺ = Subspace ℝ⁺S

ℝ⁰⁺S : Subtype ℝ ℓ-one
ℝ⁰⁺S x = 0# ≤ x , isProp-≤

ℝ⁰⁺ : Type₁
ℝ⁰⁺ = Subspace ℝ⁰⁺S

_≤≥_ : ℝ -> ℝ -> Type₁
x ≤≥ a = ∥ (x ≤ a) ⊎ (a ≤ x) ∥

ℝ≤≥S : ℝ -> Subtype ℝ ℓ-one
ℝ≤≥S a x = x ≤≥ a , squash

ℝ≤≥ : ℝ -> Type₁
ℝ≤≥ a = Subspace (ℝ≤≥S a)

ℝ≤≥0S : Subtype ℝ ℓ-one
ℝ≤≥0S = ℝ≤≥S 0#

ℝ≤≥0 : Type₁
ℝ≤≥0 = ℝ≤≥ 0#

ℝ#S : ℝ -> Subtype ℝ ℓ-one
ℝ#S a x = (x # a) , isProp-#

ℝ# : ℝ -> Type₁
ℝ# a = Subspace (ℝ#S a)
