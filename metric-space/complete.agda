{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.complete where

open import base
open import sequence
open import real
open import order
open import order.instances.nat
open import real.subspace
open import relation
open import truncation
open import metric-space
open import net
open import metric-space.continuous


module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where

  isCauchy : {ℓI ℓ≼ : Level} -> Pred (Net D ℓI ℓ≼) (ℓ-max* 3 ℓI ℓ≼ ℓ-one)
  isCauchy N =
    (ε : ℝ⁺) -> ∃[ n ∈ N.I ] ((m₁ m₂ : N.I) -> N.≼ n m₁ -> N.≼ n m₂ ->
                              εClose ε (N.f m₁) (N.f m₂))
    where
    module N = Net N

  record isLimit {ℓI ℓ≼ : Level} (n : Net D ℓI ℓ≼) (lim : D) : Type (ℓ-max* 3 ℓI ℓ≼ ℓ-one) where
    no-eta-equality
    field
      close : (ε : ℝ⁺) -> isEventually n (εClose ε lim)

module _ {ℓD : Level} (D : Type ℓD) {{MS : MetricSpaceStr D}} where
  isComplete : (ℓI ℓ≼ : Level) -> Type (ℓ-max* 4 (ℓ-suc ℓI) (ℓ-suc ℓ≼) ℓ-one ℓD)
  isComplete ℓI ℓ≼ = ∀ (s : Net D ℓI ℓ≼) -> Σ D (isLimit s)

  isComplete₀ : Type (ℓ-max ℓ-one ℓD)
  isComplete₀ = ∀ (n : Net D ℓ-zero ℓ-zero) -> isCauchy n -> Σ D (isLimit n)
