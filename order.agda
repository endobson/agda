{-# OPTIONS --cubical --safe --exact-split #-}

module order where

open import base
open import hlevel
open import relation
open import truncation

private
  variable
    ℓ : Level

record LinearOrderStr (D : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    _<_ : D -> D -> Type ℓ
    isProp-< : (x y : D) -> isProp (x < y)
    irrefl-< : Irreflexive _<_
    trans-< : Transitive _<_
    comparison-< : Comparison _<_
    connected-< : Connected _<_

  _>_ : D -> D -> Type ℓ
  x > y = y < x


module _ {D : Type ℓ} {{S : LinearOrderStr D}} where
  open LinearOrderStr S public
