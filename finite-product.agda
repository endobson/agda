{-# OPTIONS --cubical --safe --exact-split #-}

module finite-product where

open import additive-group
open import base
open import finite-commutative-monoid
open import finset
open import semiring

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    CM = Semiring.*-CommMonoid S

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    finiteProduct : (I -> D) -> D
    finiteProduct = finiteMerge CM

  finiteProductᵉ : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
  finiteProductᵉ = finiteMergeᵉ CM
