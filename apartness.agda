{-# OPTIONS --cubical --safe --exact-split #-}

module apartness where

open import base
open import relation
open import truncation

record TightApartnessStr {ℓD : Level} (D : Type ℓD) (ℓ : Level) : Type (ℓ-max ℓD (ℓ-suc ℓ)) where
  field
    _#_ : Rel D ℓ
    TightApartness-# : TightApartness _#_

  tight-# : Tight _#_
  tight-# = fst TightApartness-#

  irrefl-# : Irreflexive _#_
  irrefl-# = fst (snd TightApartness-#)

  irrefl-path-# : IrreflexivePath _#_
  irrefl-path-# = Irreflexive->IrreflexivePath _#_ irrefl-#

module _ {ℓD ℓ# : Level} {D : Type ℓD} {{TA : TightApartnessStr D ℓ#}} where
  open TightApartnessStr TA public using
    ( _#_
    ; tight-#
    ; irrefl-#
    ; irrefl-path-#
    )
