{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.bounds where

open import additive-group
open import additive-group.instances.real
open import base
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import real
open import real.distance
open import subset
open import subset.subspace
open import truncation

opaque
  isContinuous-lower-bound :
    {ℓS : Level} {S : Subtype ℝ ℓS} {f : Subspace S -> ℝ}
    (c : isContinuous f) -> ∀ (x∈@(x , _) : Subspace S) {b} -> b < f x∈ ->
    ∃[ δ ∈ ℝ⁺ ] ∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> b < f y∈
  isContinuous-lower-bound {S = S} {f} (isContinuous-cons c) x∈@(x , _) {b} b<fx =
    ∥-map handle (c x∈ ε⁺)
    where
    ε : ℝ
    ε = diff b (f x∈)
    0<ε : 0# < ε
    0<ε = diff-0<⁺ b<fx
    ε⁺ : ℝ⁺
    ε⁺ = ε , 0<ε
    handle :
      Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> εClose ε⁺ (f x∈) (f y∈)) ->
      Σ[ δ ∈ ℝ⁺ ] ∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> b < f y∈
    handle (δ , close) = (δ , lower-bound)
      where
      lower-bound : ∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> b < f y∈
      lower-bound y∈ dxy<δ =
        distance-diff-<₂ (trans-=-< (distance-commuteᵉ (f y∈) (f x∈)) (close y∈ dxy<δ))

  isContinuous-upper-bound :
    {ℓS : Level} {S : Subtype ℝ ℓS} {f : Subspace S -> ℝ}
    (c : isContinuous f) -> ∀ (x∈@(x , _) : Subspace S) {b} -> f x∈ < b ->
    ∃[ δ ∈ ℝ⁺ ] ∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> f y∈ < b
  isContinuous-upper-bound {S = S} {f} (isContinuous-cons c) x∈@(x , _) {b} fx<b =
    ∥-map handle (c x∈ ε⁺)
    where
    ε : ℝ
    ε = diff (f x∈) b
    0<ε : 0# < ε
    0<ε = diff-0<⁺ fx<b
    ε⁺ : ℝ⁺
    ε⁺ = ε , 0<ε
    handle :
      Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> εClose ε⁺ (f x∈) (f y∈)) ->
      Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : Subspace S) -> distance x y < δ -> f y∈ < b
    handle (δ , close) = (δ , upper-bound)
      where
      upper-bound : ∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> f y∈ < b
      upper-bound y dxy<δ = distance-diff-<₁ (close y dxy<δ)
