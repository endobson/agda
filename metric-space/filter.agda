{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.filter where

open import additive-group
open import additive-group.instances.real
open import base
open import metric-space
open import metric-space.continuous
open import metric-space.instances.subspace
open import order
open import order.instances.nat
open import order.instances.real
open import real
open import hlevel
open import real.subspace
open import relation
open import sequence
open import subset
open import filter
open import subset.subspace
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where

  isCauchy : {ℓS ℓF : Level} -> Pred (Filter D ℓS ℓF) (ℓ-max* 4 ℓD (ℓ-suc ℓS) ℓF ℓ-one)
  isCauchy F =
    (ε : ℝ⁺) -> ∃[ (s , _) ∈ F.∈ ] ∀ ((x , _) (y , _) : Subspace s) -> εClose ε x y
    where
    module F = Filter F




module _ {ℓD : Level} (D : Type ℓD) {{MS : MetricSpaceStr D}} where
  isComplete : (ℓS ℓF : Level) -> Type (ℓ-max* 4 (ℓ-suc ℓS) (ℓ-suc ℓF) ℓ-one ℓD)
  isComplete ℓS ℓF = ∀ (f : Filter D ℓS ℓF) -> isCauchy f -> Σ D (isLimit f)
