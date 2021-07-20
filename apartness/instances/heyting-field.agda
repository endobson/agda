{-# OPTIONS --cubical --safe --exact-split #-}

module apartness.instances.heyting-field where

open import apartness
open import base
open import heyting-field
open import ring
open import semiring

module _ {ℓD : Level} {D : Type ℓD} {S : Semiring D} {R : Ring S}
         {{F : Field R}} where
  instance
    TightApartnessStr-Field : TightApartnessStr D ℓD
    TightApartnessStr-Field = Field.TightApartnessStr-f# F
