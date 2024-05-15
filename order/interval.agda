{-# OPTIONS --cubical --safe --exact-split #-}

module order.interval where

open import base
open import order
open import relation

module _ {ℓD ℓ< : Level} (D : Type ℓD) {D< : Rel D ℓ<}
         {{LO : isLinearOrder D<}} where

  record OI : Type (ℓ-max ℓD ℓ<) where
    constructor oi
    field
      {l} : D
      {u} : D
      l<u : l < u

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {{LO : isLinearOrder D<}} where

  _∈OI_ : D -> OI D -> Type ℓ<
  _∈OI_ x i = (OI.l i < x) × (x < OI.u i)

  _⊂OI_ : OI D -> OI D -> Type ℓ<
  _⊂OI_ ia ib = (OI.l ib < OI.l ia) × (OI.u ia < OI.u ib)

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{CO : CompatibleOrderStr LO PO}} where
  private
    instance
      ILO = LO
      IPO = PO

  _⊆OI_ : OI D -> OI D -> Type ℓ≤
  _⊆OI_ ia ib = (OI.l ib ≤ OI.l ia) × (OI.u ia ≤ OI.u ib)
