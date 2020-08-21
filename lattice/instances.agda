{-# OPTIONS --cubical --safe --exact-split #-}

module lattice.instances where

open import base
open import relation
open import nat
open import lattice

≤# : RawLattice Nat
RawLattice._≼_ ≤# = _≤_
RawLattice._∧_ ≤# = min
RawLattice._∨_ ≤# = max

instance
  open IsLattice
  open Supremum
  open Infimum

  isLattice-≤ : IsLattice ≤#
  isLattice-≤ .partial-order = (trans-≤ , (\ {x} -> same-≤ x) , ≤-antisym)
  isLattice-≤ .supremum .x≼x∨y = \_ _ -> ≤-max-left
  isLattice-≤ .supremum .y≼x∨y = \_ _ -> ≤-max-right
  isLattice-≤ .supremum .∨-least = \_ _ _ -> ≤-max-least
  isLattice-≤ .infimum .x∧y≼x = \_ _ -> ≤-min-left
  isLattice-≤ .infimum .x∧y≼y = \_ _ -> ≤-min-right
  isLattice-≤ .infimum .∧-greatest = \_ _ _ -> ≤-min-greatest
