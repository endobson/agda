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


module _ {D : Type ℓD} {{S : LinearOrderStr D ℓ<}} where
  open LinearOrderStr S public


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

record CompatibleOrderStr
         (D : Type ℓD) (ℓ< ℓ≤ : Level)
         (<-Str : LinearOrderStr D ℓ<)
         (≤-Str : TotalOrderStr D ℓ≤) : Type (ℓ-max (ℓ-max ℓ≤ ℓ<) ℓD) where
  private
    instance
      <-Str-I = <-Str
      ≤-Str-i = ≤-Str

  field
    weaken-< : {d1 d2 : D} -> d1 < d2 -> d1 ≤ d2
    strengthen-≤-≮ : {d1 d2 : D} -> d1 ≤ d2 -> d1 ≮ d2 -> d1 == d2
    strengthen-≤-≠ : {d1 d2 : D} -> d1 ≤ d2 -> d1 != d2 -> d1 < d2
