{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import order
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-additive-group.minmax
open import real
open import real.order
open import real.rational
open import subset
open import truncation

-- TODO move most of this file to generic metric space definitions

distance : ℝ -> ℝ -> ℝ
distance x y = abs (diff x y)

opaque
  path->zero-distance : {x y : ℝ} -> x == y -> distance x y == 0#
  path->zero-distance p = cong abs (+-left (sym p) >=> +-inverse) >=> abs-0≤-path refl-≤

  distance-triangle : {x y z : ℝ} -> distance x z ≤ (distance x y + distance y z)
  distance-triangle =
    trans-=-≤
      (cong2 max (sym diff-trans) (cong -_ (sym diff-trans) >=> minus-distrib-plus))
      max-+-swap

  distance-commute : {x y : ℝ} -> distance x y == distance y x
  distance-commute = cong abs diff-anticommute >=> abs-minus

isContinuousAt : {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) (x : ∈-Subtype S) ->
                 Type (ℓ-max ℓS ℓ-one)
isContinuousAt S f x@(x' , _) =
  ∀ ((ε , _) : ℝ⁺) -> ∃[ (δ , _) ∈ ℝ⁺ ] ∀ (y@(y' , _) : ∈-Subtype S) ->
    distance x' y' < δ -> distance (f x) (f y) < ε

isContinuous : {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) -> Type (ℓ-max ℓS ℓ-one)
isContinuous S f = ∀ x -> isContinuousAt S f x

isContinuousℚAt : {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) (x : ∈-Subtype S) ->
                 Type (ℓ-max ℓS ℓ-one)
isContinuousℚAt S f x@(x' , _) =
  ∀ ((ε , _) : ℝ⁺) -> ∃[ (δ , _) ∈ ℚ⁺ ] ∀ (y@(y' , _) : ∈-Subtype S) ->
    distance x' y' < ℚ->ℝ δ -> distance (f x) (f y) < ε

isContinuousℚ : {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) -> Type (ℓ-max ℓS ℓ-one)
isContinuousℚ S f = ∀ x -> isContinuousℚAt S f x

opaque
  isContinuous->isContinuousℚ :
    {ℓS : Level} (S : Subtype ℝ ℓS) {f : ∈-Subtype S -> ℝ} ->
    isContinuous S f -> isContinuousℚ S f
  isContinuous->isContinuousℚ S {f} c x∈@(x , _) ε⁺@(ε , _) = ∥-bind handle (c x∈ ε⁺)
    where
    handle : (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype S) ->
                 distance x y < δ -> distance (f x∈) (f y∈) < ε) ->
             ∃[ (δ , _) ∈ ℚ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype S) ->
                distance x y < ℚ->ℝ δ -> distance (f x∈) (f y∈) < ε
    handle ((δ1 , 0<δ1) , δ1-close) = ∥-map handle2 0<δ1
      where
      handle2 : 0# ℝ<' δ1 -> _
      handle2 (ℝ<'-cons δ2 0U-δ2 δ1L-δ2) = (δ2 , U->ℚ< 0U-δ2) , δ2-close
        where
        δ2-close : ∀ (y∈@(y , _) : ∈-Subtype S) -> distance x y < ℚ->ℝ δ2 -> distance (f x∈) (f y∈) < ε
        δ2-close y∈ d<δ2 = δ1-close y∈ (trans-< d<δ2 (L->ℝ< δ1L-δ2))
