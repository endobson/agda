{-# OPTIONS --cubical --safe --exact-split #-}

module real.filter-complete where

open import additive-group
open import additive-group.instances.real
open import base
open import hlevel.base
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import equality
open import metric-space
open import metric-space.filter
open import metric-space.continuous
open import metric-space.instances.real
open import order
open import ordered-field
open import ordered-field.mean
open import order.minmax
open import order.minmax.instances.real
open import order.instances.rational
open import order.instances.real
open import ordered-semiring
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-semiring.instances.real
open import ordered-semiring.instances.rational
open import rational
open import nat.arithmetic
open import real
open import real.order
open import real.subspace
open import real.sequence
open import real.rational
open import real.arithmetic.rational
open import relation hiding (U)
open import ring.implementations.real
open import ring.implementations.rational
open import semiring
open import subset
open import subset.subspace
open import truncation
open import filter





isComplete₀-ℝ : isComplete ℝ ℓ-zero ℓ-zero
isComplete₀-ℝ F cauchy = ?
  where
  module F = Filter F

  L : Pred ℚ ℓ-zero
  L q = F.P q⁺S
    where
    q⁺S : Subtype ℝ ℓ-zero
    q⁺S x = Real.L x q , Real.isProp-L x q
