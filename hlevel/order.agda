{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.order where

open import base
open import equality
open import hlevel.base
open import hlevel.hedberg
open import order
open import relation

module _ {ℓA ℓ< : Level} (A : Type ℓA) {A< : Rel A ℓ<} {{LO : isLinearOrder A<}} where
  private
    Stable== : (x y : A) -> Stable (x == y)
    Stable== x y ¬¬x=y = connected-< (\x<y -> ¬¬x=y (\x=y -> irrefl-path-< x=y x<y))
                                     (\y<x -> ¬¬x=y (\x=y -> irrefl-path-< (sym x=y) y<x))

  isSet-LinearlyOrdered : isSet A
  isSet-LinearlyOrdered = Stable==->isSet Stable==
