{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.squeeze where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import real
open import real.subspace
open import subset
open import subset.subspace
open import truncation

opaque
  squeeze-isContinuousAt : {ℓS : Level} {S : Subtype ℝ ℓS}
    (f g h : Subspace S -> ℝ) (x∈ : Subspace S) ->
    (∀ y∈ -> f y∈ ≤ g y∈) ->
    (∀ y∈ -> g y∈ ≤ h y∈) ->
    isContinuousAt f x∈ ->
    isContinuousAt h x∈ ->
    f x∈ == h x∈ ->
    isContinuousAt g x∈
  squeeze-isContinuousAt f g h x∈ f≤g g≤h cont-f cont-h fx=hx ε⁺@(ε , 0<ε) =
    ∥-map2 handle (cont-f ε⁺) (cont-h ε⁺)
    where
    handle : Σ[ δf ∈ ℝ⁺ ] (∀ y∈ -> εClose δf x∈ y∈ -> εClose ε⁺ (f x∈) (f y∈)) ->
             Σ[ δh ∈ ℝ⁺ ] (∀ y∈ -> εClose δh x∈ y∈ -> εClose ε⁺ (h x∈) (h y∈)) ->
             Σ[ δg ∈ ℝ⁺ ] (∀ y∈ -> εClose δg x∈ y∈ -> εClose ε⁺ (g x∈) (g y∈))
    handle ((δf , 0<δf) , close-f) ((δh , 0<δh) , close-h) = ((δg , 0<δg) , close-g)
      where
      δg : ℝ
      δg = min δf δh
      0<δg : 0# < δg
      0<δg = min-greatest-< 0<δf 0<δh
      close-g : ∀ y∈ -> εClose (δg , 0<δg) x∈ y∈ -> εClose ε⁺ (g x∈) (g y∈)
      close-g y∈ dxy<δg = max-least-< dgxgy<ε (trans-=-< (sym diff-anticommute) dgygx<ε)
        where
        dfxfy<ε : εClose ε⁺ (f x∈) (f y∈)
        dfxfy<ε = close-f y∈ (trans-<-≤ dxy<δg min-≤-left)
        dhxhy<ε : εClose ε⁺ (h x∈) (h y∈)
        dhxhy<ε = close-h y∈ (trans-<-≤ dxy<δg min-≤-right)

        dgxgy<ε : diff (g x∈) (g y∈) < ε
        dgxgy<ε = trans-≤-< (+-preserves-≤ (g≤h y∈) (minus-flips-≤ (trans-=-≤ (sym fx=hx) (f≤g x∈))))
                            (trans-≤-< abs-≤ dhxhy<ε)

        dgygx<ε : diff (g y∈) (g x∈) < ε
        dgygx<ε = trans-≤-< (+-preserves-≤ (trans-≤-= (g≤h x∈) (sym fx=hx)) (minus-flips-≤ (f≤g y∈)))
                            (trans-≤-< (trans-≤-= abs-≤ (distance-commuteᵉ (f y∈) (f x∈))) dfxfy<ε)
