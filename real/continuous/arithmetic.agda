{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.arithmetic where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import heyting-field.instances.real
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.distance
open import real.subspace
open import ring.implementations.real
open import semiring
open import subset.subspace
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isContinuousAt-+ : {f g : D -> ℝ} {x : D} -> isContinuousAt f x -> isContinuousAt g x ->
                       isContinuousAt (\x -> f x + g x) x
    isContinuousAt-+ {f} {g} {x} cf cg ε⁺@(ε , 0<ε) =
      ∥-map2 handle (cf ε/2⁺) (cg ε/2⁺)
      where
      ε/2 : ℝ
      ε/2 = 1/2 * ε
      0<ε/2 : 0# < ε/2
      0<ε/2 = *-preserves-0< 0<1/2 0<ε
      ε/2⁺ : ℝ⁺
      ε/2⁺ = ε/2 , 0<ε/2

      handle :
        Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε/2⁺ (f x) (f y)) ->
        Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε/2⁺ (g x) (g y)) ->
        Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (f x + g x) (f y + g y))
      handle ((δf , 0<δf) , f-close) ((δg , 0<δg) , g-close) = (δ , 0<δ) , fg-close
        where
        δ : ℝ
        δ = min δf δg
        0<δ : 0# < δ
        0<δ = min-greatest-< 0<δf 0<δg

        fg-close : (y : D) -> distance x y < δ -> distance (f x + g x) (f y + g y) < ε
        fg-close y dxy<δ =
          trans-≤-< distance-+-swap
            (trans-<-= (+-preserves-< dfxfy<ε/2 dgxgy<ε/2) 1/2-path)
          where
          dxy<δf : distance x y < δf
          dxy<δf = trans-<-≤ dxy<δ min-≤-left

          dxy<δg : distance x y < δg
          dxy<δg = trans-<-≤ dxy<δ min-≤-right

          dfxfy<ε/2 : distance (f x) (f y) < ε/2
          dfxfy<ε/2 = f-close y dxy<δf

          dgxgy<ε/2 : distance (g x) (g y) < ε/2
          dgxgy<ε/2 = g-close y dxy<δg

    isContinuous-+ : {f g : D -> ℝ} -> isContinuous f -> isContinuous g ->
                     isContinuous (\x -> f x + g x)
    isContinuous-+ {f} {g} (isContinuous-cons cf) (isContinuous-cons cg) .isContinuous.at x =
      isContinuousAt-+ (cf x) (cg x)

    isContinuous-+₁ : {k : ℝ} -> {f : D -> ℝ} -> isContinuous f -> isContinuous (\x -> k + f x)
    isContinuous-+₁ {k} cf = isContinuous-+ (isContinuous-const k) cf
    isContinuous-+₂ : {k : ℝ} -> {f : D -> ℝ} -> isContinuous f -> isContinuous (\x -> f x + k)
    isContinuous-+₂ {k} cf = isContinuous-+ cf (isContinuous-const k)

  opaque
    isContinuousAt-minus :
      {f : D -> ℝ} {x : D} -> isContinuousAt f x -> isContinuousAt (\x -> - (f x)) x
    isContinuousAt-minus {f} {x} cf ε = ∥-map handle (cf ε)
      where
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε (f x) (f y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε (- (f x)) (- (f y)))
      handle (δ , close) = (δ , \y εC -> trans-=-< (sym minus-preserves-distance) (close y εC))

    isContinuous-minus : {f : D -> ℝ} -> isContinuous f -> isContinuous (\x -> - (f x))
    isContinuous-minus (isContinuous-cons cf) .isContinuous.at x = isContinuousAt-minus (cf x)

  opaque
    isContinuousAt-diff : {f g : D -> ℝ} {x : D} -> isContinuousAt f x -> isContinuousAt g x ->
                          isContinuousAt (\x -> diff (f x) (g x)) x
    isContinuousAt-diff cf cg = isContinuousAt-+ cg (isContinuousAt-minus cf)

    isContinuous-diff : {f g : D -> ℝ} -> isContinuous f -> isContinuous g ->
                        isContinuous (\x -> diff (f x) (g x))
    isContinuous-diff cf cg = isContinuous-+ cg (isContinuous-minus cf)
