{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.maximum where

open import finite-commutative-monoid
open import finset
open import base
open import commutative-monoid
open import order
open import order.minmax
open import order.minmax.commutative-monoid

module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<}
         {{Max : MaxOperationStr LO}}
         {{Min : GlobalMinOperationStr LO}}
         {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
  finiteMax : (f : I -> D) -> D
  finiteMax f = finiteMerge MaxCommMonoid f
