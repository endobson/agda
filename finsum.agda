{-# OPTIONS --cubical --safe --exact-split #-}

module finsum where

open import additive-group
open import base
open import finite-commutative-monoid
open import finset


module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}} where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    finiteSum : (I -> D) -> D
    finiteSum = finiteMerge CM

  finiteSumᵉ : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
  finiteSumᵉ = finiteMergeᵉ CM
