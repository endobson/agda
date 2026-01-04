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

  record _∈OI_ (x : D) (i : OI D) : Type ℓ< where
    constructor _,_
    field
      l<x : OI.l i < x
      x<u : x < OI.u i

  record _⊂OI_ (ia : OI D) (ib : OI D) : Type ℓ< where
    constructor _,_
    field
      l<l : OI.l ib < OI.l ia
      u<u : OI.u ia < OI.u ib

  trans-∈OI-⊂OI : {x : D} {i1 i2 : OI D} -> x ∈OI i1 -> i1 ⊂OI i2 -> x ∈OI i2
  trans-∈OI-⊂OI (l1<x , x<u1) (l2<l1 , u1<u2) = (trans-< l2<l1 l1<x , trans-< x<u1 u1<u2)

  trans-⊂OI : {i1 i2 i3 : OI D} -> i1 ⊂OI i2 -> i2 ⊂OI i3 -> i1 ⊂OI i3
  trans-⊂OI (l2<l1 , u1<u2) (l3<l2 , u2<u3) = (trans-< l3<l2 l2<l1 , trans-< u1<u2 u2<u3)


module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{LO : isLinearOrder D<}} {{PO : isPartialOrder D≤}}
         {{CO : CompatibleOrderStr LO PO}} where

  record _⊆OI_ (ia : OI D) (ib : OI D) : Type ℓ≤ where
    constructor _,_
    field
      l<l : OI.l ib ≤ OI.l ia
      u<u : OI.u ia ≤ OI.u ib

  weaken-⊂OI : {i1 i2 : OI D} -> i1 ⊂OI i2 -> i1 ⊆OI i2
  weaken-⊂OI (l2<l1 , u1<u2) = (weaken-< l2<l1 , weaken-< u1<u2)

  trans-∈OI-⊆OI : {x : D} {i1 i2 : OI D} -> x ∈OI i1 -> i1 ⊆OI i2 -> x ∈OI i2
  trans-∈OI-⊆OI (l1<x , x<u1) (l2≤l1 , u1≤u2) = (trans-≤-< l2≤l1 l1<x , trans-<-≤ x<u1 u1≤u2)

  trans-⊆OI : {i1 i2 i3 : OI D} -> i1 ⊆OI i2 -> i2 ⊆OI i3 -> i1 ⊆OI i3
  trans-⊆OI (l2≤l1 , u1≤u2) (l3≤l2 , u2≤u3) = (trans-≤ l3≤l2 l2≤l1 , trans-≤ u1≤u2 u2≤u3)

  trans-⊂OI-⊆OI : {i1 i2 i3 : OI D} -> i1 ⊂OI i2 -> i2 ⊆OI i3 -> i1 ⊂OI i3
  trans-⊂OI-⊆OI (l2<l1 , u1<u2) (l3≤l2 , u2≤u3) = (trans-≤-< l3≤l2 l2<l1 , trans-<-≤ u1<u2 u2≤u3)

  trans-⊆OI-⊂OI : {i1 i2 i3 : OI D} -> i1 ⊆OI i2 -> i2 ⊂OI i3 -> i1 ⊂OI i3
  trans-⊆OI-⊂OI (l2≤l1 , u1≤u2) (l3<l2 , u2<u3) = (trans-<-≤ l3<l2 l2≤l1 , trans-≤-< u1≤u2 u2<u3)
