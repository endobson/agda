{-# OPTIONS --cubical --safe --exact-split #-}

module hit-int where

open import base
open import isomorphism
open import cubical

import int

data Int : Type₀ where
  nonneg : Nat -> Int
  nonpos : Nat -> Int
  same-zero : nonneg 0 == nonpos 0

int : Nat -> Int
int = nonneg

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

add1 : Int -> Int
add1 (nonneg x) = nonneg (suc x)
add1 (nonpos zero) = (add1 (nonneg zero))
add1 (nonpos (suc x)) = (nonpos x)
add1 (same-zero i) = nonneg (suc zero)

sub1 : Int -> Int
sub1 (nonneg (suc x)) = nonneg x
sub1 (nonneg zero) = (sub1 (nonpos zero))
sub1 (nonpos x) = (nonpos (suc x))
sub1 (same-zero i) = nonpos (suc zero)

add1-sub1 : ∀ z -> add1 (sub1 z) == z
add1-sub1 (nonneg (suc x)) = refl
add1-sub1 (nonneg zero) i = same-zero (~ i)
add1-sub1 (nonpos x) = refl
add1-sub1 (same-zero i) j = same-zero (i ∨ (~ j))

sub1-add1 : ∀ z -> sub1 (add1 z) == z
sub1-add1 (nonneg x) = refl
sub1-add1 (nonpos zero) i = same-zero i
sub1-add1 (nonpos (suc x)) = refl
sub1-add1 (same-zero i) j = same-zero (i ∧ j)
