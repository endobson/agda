{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.arithmetic.absolute-value where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import functions
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import real
open import real.subspace
open import subset.subspace
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isContinuousAt-abs :
      {f : D -> ℝ} {x : D} -> isContinuousAt f x  -> isContinuousAt (\x -> abs (f x)) x
    isContinuousAt-abs {f} {x} cont-f ε⁺@(ε , _) = ∥-map handle (cont-f ε⁺)
      where
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (f x) (f y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (abs (f x)) (abs (f y)))
      handle (δ⁺@(δ , _) , close) = (δ⁺ , close')
        where
        close' : ∀ y -> εClose δ⁺ x y -> εClose ε⁺ (abs (f x)) (abs (f y))
        close' y dxy<δ = max-least-< dafxafy<ε (trans-=-< (sym diff-anticommute) dafyafx<ε)
          where
          dafxafy<ε : diff (abs (f x)) (abs (f y)) < ε
          dafxafy<ε = trans-≤-< diff-abs≤abs-diff (close y dxy<δ)
          dafyafx<ε : diff (abs (f y)) (abs (f x)) < ε
          dafyafx<ε = trans-≤-< diff-abs≤abs-diff
                        (trans-=-< (distance-commuteᵉ (f y) (f x)) (close y dxy<δ))

    isContinuous-abs : {f : D -> ℝ} -> isContinuous f -> isContinuous (abs ∘ f)
    isContinuous-abs (isContinuous-cons cf) .isContinuous.at x = isContinuousAt-abs (cf x)
