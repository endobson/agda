{-# OPTIONS --cubical --safe --exact-split #-}

module apartness where

open import base
open import functions
open import hlevel
open import relation
open import truncation

record isTightApartness {ℓD ℓ# : Level} {D : Type ℓD} (_#_ : Rel D ℓ#) : Type (ℓ-max ℓD ℓ#) where
  field
    tight-# : Tight _#_
    irrefl-# : Irreflexive _#_
    sym-# : Symmetric _#_
    comparison-# : Comparison _#_
    isProp-# : {d1 d2 : D} -> isProp (d1 # d2)

module _ {ℓD ℓ# : Level} {D : Type ℓD} {ap : Rel D ℓ#} {{TA : isTightApartness ap}} where
  open isTightApartness TA public

  _#_ : Rel D ℓ#
  _#_ = ap

  irrefl-path-# : IrreflexivePath _#_
  irrefl-path-# = Irreflexive->IrreflexivePath _#_ irrefl-#


module _ {ℓD1 ℓD2 ℓ#1 ℓ#2 : Level} {D1 : Type ℓD1} {D2 : Type ℓD2}
         {#1 : Rel D1 ℓ#1} {#2 : Rel D2 ℓ#2}
         {{TA1 : isTightApartness #1}} {{TA2 : isTightApartness #2}}
  where

  StronglyInjective : Pred (D1 -> D2) (ℓ-max* 3 ℓD1 ℓ#1 ℓ#2)
  StronglyInjective f = {a b : D1} -> a # b -> f a # f b

module _ {ℓD1 ℓD2 ℓD3 ℓ#1 ℓ#2 ℓ#3 : Level} {D1 : Type ℓD1} {D2 : Type ℓD2} {D3 : Type ℓD3}
         {#1 : Rel D1 ℓ#1} {#2 : Rel D2 ℓ#2} {#3 : Rel D3 ℓ#3}
         {{TA1 : isTightApartness #1}} {{TA2 : isTightApartness #2}} {{TA3 : isTightApartness #3}}
  where

  ∘-StronglyInjective : {f : D2 -> D3} {g : D1 -> D2} -> StronglyInjective f -> StronglyInjective g ->
                        StronglyInjective (f ∘ g)
  ∘-StronglyInjective f' g' = f' ∘ g'
