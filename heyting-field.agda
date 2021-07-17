{-# OPTIONS --cubical --safe --exact-split #-}

module heyting-field where

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

  _#_ : D -> D -> Type ℓ
  x # y = R.isUnit (y + (- x))

  field
    tight-apartness-# : TightApartness _#_

  sym-# : Symmetric _#_
  sym-# = fst (snd (snd tight-apartness-#))

  1#0 : 1# # 0#
  1#0 = sym-# (subst R.isUnit (sym +-right-zero >=> +-right (sym minus-zero)) R.isUnit-one)
