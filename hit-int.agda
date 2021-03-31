{-# OPTIONS --cubical --safe --exact-split #-}

module hit-int where

open import base
open import nat
open import isomorphism
open import equivalence
open import cubical
open import equality

import int

data Int : Type₀ where
  nonneg : Nat -> Int
  nonpos : Nat -> Int
  same-zero : nonneg 0 == nonpos 0

Int-eq : Int ≃ int.Int
Int-eq = isoToEquiv i
  where
  open Iso
  i : Iso Int int.Int
  i .fun (nonneg n)       = (int.nonneg n)
  i .fun (nonpos zero)    = (int.nonneg zero)
  i .fun (nonpos (suc n)) = (int.neg n)
  i .fun (same-zero i)    = (int.nonneg zero)
  i .inv (int.nonneg n)   = (nonneg n)
  i .inv (int.neg n)      = (nonpos (suc n))
  i .rightInv (int.nonneg n)  = refl
  i .rightInv (int.neg n)     = refl
  i .leftInv (nonneg n)       = refl
  i .leftInv (nonpos zero)    = same-zero
  i .leftInv (nonpos (suc n)) = refl
  i .leftInv (same-zero i)    = (\j -> same-zero (j ∧ i))
