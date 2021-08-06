{-# OPTIONS --cubical --safe --exact-split #-}

module order where

open import base
open import equality
open import hlevel
open import relation
open import truncation

private
  variable
    ℓD ℓ< : Level

record LinearOrderStr (D : Type ℓD) (ℓ< : Level) : Type (ℓ-max (ℓ-suc ℓ<) ℓD) where
  field
    _<_ : D -> D -> Type ℓ<
    isProp-< : (x y : D) -> isProp (x < y)
    irrefl-< : Irreflexive _<_
    trans-< : Transitive _<_
    comparison-< : Comparison _<_
    connected-< : Connected _<_

  _>_ : D -> D -> Type ℓ<
  x > y = y < x

  _≮_ : D -> D -> Type ℓ<
  x ≮ y = ¬ (x < y)

  _≯_ : D -> D -> Type ℓ<
  x ≯ y = ¬ (x > y)

  asym-< : Asymmetric _<_
  asym-< x<y y<x = irrefl-< (trans-< x<y y<x)


module _ {D : Type ℓD} {{S : LinearOrderStr D ℓ<}} where
  open LinearOrderStr S public

  abstract
    trans-≮ : Transitive _≮_
    trans-≮ {a} {b} {c} a≮b b≮c a<c = unsquash isPropBot (∥-map handle (comparison-< a b c a<c))
      where
      handle : (a < b) ⊎ (b < c) -> Bot
      handle (inj-l a<b) = a≮b a<b
      handle (inj-r b<c) = b≮c b<c



record TotalOrderStr (D : Type ℓD) (ℓ≤ : Level) : Type (ℓ-max (ℓ-suc ℓ≤) ℓD) where
  field
    _≤_ : D -> D -> Type ℓ≤
    isProp-≤ : (x y : D) -> isProp (x ≤ y)
    refl-≤ : Reflexive _≤_
    trans-≤ : Transitive _≤_
    antisym-≤ : Antisymmetric _≤_
    connex-≤ : Connex _≤_

  _≥_ : D -> D -> Type ℓ≤
  x ≥ y = y ≤ x

module _ {D : Type ℓD} {{S : TotalOrderStr D ℓ<}} where
  open TotalOrderStr S public

module _ (D : Type ℓD) (ℓ< ℓ≤ : Level)
         (<-Str : LinearOrderStr D ℓ<)
         (≤-Str : TotalOrderStr D ℓ≤) where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-i = ≤-Str

  record CompatibleOrderStr : Type (ℓ-max (ℓ-max ℓ≤ ℓ<) ℓD) where
    field
      weaken-< : {d1 d2 : D} -> d1 < d2 -> d1 ≤ d2
      strengthen-≤-≮ : {d1 d2 : D} -> d1 ≤ d2 -> d1 ≮ d2 -> d1 == d2
      strengthen-≤-≠ : {d1 d2 : D} -> d1 ≤ d2 -> d1 != d2 -> d1 < d2


record DecidableCompatibleOrderStr
         (D : Type ℓD) (ℓ< ℓ≤ : Level)
         (<-Str : LinearOrderStr D ℓ<)
         (≤-Str : TotalOrderStr D ℓ≤) : Type (ℓ-max (ℓ-max ℓ≤ ℓ<) ℓD) where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-i = ≤-Str

  field
    split-< : (d1 d2 : D) -> (d1 < d2) ⊎ (d2 ≤ d1)

module _ {D : Type ℓD} {ℓ< ℓ≤ : Level} {<-Str : LinearOrderStr D ℓ<} {≤-Str : TotalOrderStr D ℓ≤}
         {{S : DecidableCompatibleOrderStr D ℓ< ℓ≤ <-Str ≤-Str}} where
  open DecidableCompatibleOrderStr S public
