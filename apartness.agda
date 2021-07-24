{-# OPTIONS --cubical --safe --exact-split #-}

module apartness where

open import base
open import hlevel
open import relation
open import truncation

-- TODO: Figure out the right way to make this level polymorphic.
record TightApartnessStr {ℓD : Level} (D : Type ℓD) : Type (ℓ-suc ℓD) where
  field
    _#_ : Rel D ℓD
    TightApartness-# : TightApartness _#_
    isProp-# : isPropValued _#_

  tight-# : Tight _#_
  tight-# = fst TightApartness-#

  irrefl-# : Irreflexive _#_
  irrefl-# = fst (snd TightApartness-#)

  irrefl-path-# : IrreflexivePath _#_
  irrefl-path-# = Irreflexive->IrreflexivePath _#_ irrefl-#

  sym-# : Symmetric _#_
  sym-# = fst (snd (snd TightApartness-#))

  comparison-# : Comparison _#_
  comparison-# = snd (snd (snd TightApartness-#))


module _ {ℓD : Level} {D : Type ℓD} {{TA : TightApartnessStr D}} where
  open TightApartnessStr TA public using
    ( _#_
    ; tight-#
    ; irrefl-#
    ; irrefl-path-#
    ; sym-#
    ; comparison-#
    )

  isProp-# : {d1 d2 : D} -> isProp (d1 # d2)
  isProp-# = TightApartnessStr.isProp-# TA _ _
