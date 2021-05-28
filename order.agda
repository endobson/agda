{-# OPTIONS --cubical --safe --exact-split #-}

module order where

open import base
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


module _ {D : Type ℓD} {{S : LinearOrderStr D ℓ<}} where
  open LinearOrderStr S public
