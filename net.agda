{-# OPTIONS --cubical --safe --exact-split #-}

module net where

open import base
open import relation
open import hlevel.base
open import truncation
open import functions
open import order hiding (refl-≼ ; trans-≼)

module _ {ℓ≼ ℓD : Level} {D : Type ℓD} {_≼_ : Rel D ℓ≼} (PO : isPreOrder _≼_) where
  private
    instance
      IPO = PO

  record isDirected : Type (ℓ-max ℓ≼ ℓD) where
    field
      ∃upper-bound : (a b : D) -> ∃[ c ∈ D ] ((a ≼ c) × (b ≼ c))

record DirectedSet (ℓI ℓ≼ : Level) : Type (ℓ-max (ℓ-suc ℓI) (ℓ-suc ℓ≼)) where
  field
    Index : Type ℓI
    isSet-Index : isSet Index
    R : Rel Index ℓ≼
    isPreOrder-R : isPreOrder R
    isDirected-R : isDirected isPreOrder-R

record Net {ℓD : Level} (D : Type ℓD) (ℓI ℓ≼ : Level) : Type (ℓ-max* 3 ℓD (ℓ-suc ℓI) (ℓ-suc ℓ≼)) where
  field
    directed-set : DirectedSet ℓI ℓ≼
  I : Type ℓI
  I = DirectedSet.Index directed-set

  ≼ : Rel I ℓ≼
  ≼ = DirectedSet.R directed-set

  ∃upper-bound : (a b : I) -> ∃[ c ∈ I ] ((≼ a c) × (≼ b c))
  ∃upper-bound = isDirected.∃upper-bound (DirectedSet.isDirected-R directed-set)

  refl-≼ : Reflexive ≼
  refl-≼ = isPreOrder.refl-≼ (DirectedSet.isPreOrder-R directed-set)
  trans-≼ : Transitive ≼
  trans-≼ = isPreOrder.trans-≼ (DirectedSet.isPreOrder-R directed-set)

  field
    f : I -> D

module _ {ℓD ℓI ℓ≼ ℓS : Level} {D : Type ℓD} where

  record isEventuallyΣ (N : Net D ℓI ℓ≼) (P : Pred D ℓS) : Type (ℓ-max* 3 ℓI ℓ≼ ℓS) where
    constructor _,_
    module N = Net N
    field
      i : N.I
      prop : (∀ i2 -> N.≼ i i2 -> P (N.f i2))

  isEventually : Net D ℓI ℓ≼ -> Pred D ℓS -> Type (ℓ-max* 3 ℓI ℓ≼ ℓS)
  isEventually N P = ∥ isEventuallyΣ N P ∥

  isFrequently : Net D ℓI ℓ≼ -> Pred D ℓS -> Type _
  isFrequently N P = ∀ (i : N.I) -> ∃[ i2 ∈ N.I ] (N.≼ i i2 -> P (N.f i2))
    where
    module N = Net N

module _ {ℓA ℓB ℓI ℓ≼ : Level} {A : Type ℓA} {B : Type ℓB} where

  Net-map : (A -> B) -> Net A ℓI ℓ≼ -> Net B ℓI ℓ≼
  Net-map f n .Net.directed-set = Net.directed-set n
  Net-map f n .Net.f = f ∘ Net.f n

module _ {ℓD ℓI ℓ≼ ℓS1 ℓS2 : Level} {D : Type ℓD} where
  opaque
    isEventually-∩ : {N : Net D ℓI ℓ≼} {P1 : Pred D ℓS1} {P2 : Pred D ℓS2} ->
      isEventually N P1 -> isEventually N P2 -> isEventually N (P1 ∩ P2)
    isEventually-∩ {N} {P1} {P2} = ∥-bind2 handle
      where
      module N = Net N
      handle : isEventuallyΣ N P1 -> isEventuallyΣ N P2 -> isEventually N (P1 ∩ P2)
      handle (i1 , e1) (i2 , e2) = ∥-bind handle2 (N.∃upper-bound i1 i2)
        where
        handle2 : Σ[ i3 ∈ N.I ] (N.≼ i1 i3 × N.≼ i2 i3) -> isEventually N (P1 ∩ P2)
        handle2 (i3 , i1≼i3 , i2≼i3) =
          ∣ i3 , (\i4 i3≼i4 -> e1 i4 (N.trans-≼ i1≼i3 i3≼i4) ,
                               e2 i4 (N.trans-≼ i2≼i3 i3≼i4)) ∣

    isEventually-map : {N : Net D ℓI ℓ≼} {P1 : Pred D ℓS1} {P2 : Pred D ℓS2} ->
      (∀ d -> P1 d -> P2 d) -> isEventually N P1 -> isEventually N P2
    isEventually-map {N} {P1} {P2} f = ∥-map handle
      where
      module N = Net N
      handle : isEventuallyΣ N P1 -> isEventuallyΣ N P2
      handle (i1 , e1) = (i1 , \i2 i1≼i2 -> f (N.f i2) (e1 i2 i1≼i2))
