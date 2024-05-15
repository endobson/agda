{-# OPTIONS --cubical --safe --exact-split #-}

module order.continuous where

open import base
open import functions
open import order
open import order.interval
open import relation
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {{LO : isLinearOrder D<}} where

  isContinuousAt : D -> (D -> D) -> Type (ℓ-max ℓD ℓ<)
  isContinuousAt x f =
    ∀ (i : OI D) -> (f x ∈OI i) ->
    ∃[ i2 ∈ OI D ] (x ∈OI i2 × (∀ y -> y ∈OI i2 -> (f y) ∈OI i))

  isContinuous : (D -> D) -> Type (ℓ-max ℓD ℓ<)
  isContinuous f = ∀ x -> isContinuousAt x f

  opaque
    ∘-isContinuous : {f g : D -> D} -> isContinuous f -> isContinuous g ->
                     isContinuous (f ∘ g)
    ∘-isContinuous {f} {g} fc gc x i1 fgx∈i1 =
      ∥-bind handle (fc (g x) i1 fgx∈i1)
      where
      handle : Σ[ i2 ∈ OI D ] (g x ∈OI i2 × (∀ y -> y ∈OI i2 -> f y ∈OI i1)) ->
               ∃[ i3 ∈ OI D ] (x ∈OI i3 × (∀ z -> z ∈OI i3 -> f (g z) ∈OI i1))
      handle (i2 , gx∈i2 , f∈i1) = ∥-map handle2 (gc x i2 gx∈i2)
        where
        handle2 : Σ[ i3 ∈ OI D ] (x ∈OI i3 × (∀ z -> z ∈OI i3 -> g z ∈OI i2)) ->
                  Σ[ i3 ∈ OI D ] (x ∈OI i3 × (∀ z -> z ∈OI i3 -> f (g z) ∈OI i1))
        handle2 (i3 , x∈i3 , g∈i2) = (i3 , x∈i3 , \z z∈i3 -> f∈i1 (g z) (g∈i2 z z∈i3))
