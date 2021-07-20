{-# OPTIONS --cubical --safe --exact-split #-}

module heyting-field where

open import apartness
open import base
open import equality
open import relation
open import ring
open import semiring
open import truncation

private
  variable
    ℓ : Level

record Field {ℓ : Level} {D : Type ℓ} {S : Semiring D} (R : Ring S) : Type ℓ where
  private
    module R = Ring R
    instance
      IS = S
      IR = R

  _f#_ : D -> D -> Type ℓ
  x f# y = R.isUnit (y + (- x))

  field
    TightApartness-f# : TightApartness _f#_

  sym-f# : Symmetric _f#_
  sym-f# = fst (snd (snd TightApartness-f#))

  1#0 : 1# f# 0#
  1#0 = sym-f# (subst R.isUnit (sym +-right-zero >=> +-right (sym minus-zero)) R.isUnit-one)

  TightApartnessStr-f# : TightApartnessStr D ℓ
  TightApartnessStr-f# = record { _#_ = _f#_ ; TightApartness-# = TightApartness-f# }
