{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.base where

open import additive-group
open import base
open import equality
open import hlevel.base
open import order
open import order.instances.rational
open import rational
open import relation

record Iℚ : Type₀ where
  no-eta-equality ; pattern
  constructor Iℚ-cons
  field
    l : ℚ
    u : ℚ
    l≤u : l ≤ u

Iℚ-bounds-path : {a b : Iℚ} -> (Iℚ.l a == Iℚ.l b) -> (Iℚ.u a == Iℚ.u b) -> a == b
Iℚ-bounds-path {a@(Iℚ-cons _ _ _)} {b@(Iℚ-cons _ _ _)} pl pu = a.path
  where
  module a where
    abstract
      p≤ : PathP (\i -> (pl i) ≤ (pu i)) (Iℚ.l≤u a) (Iℚ.l≤u b)
      p≤ = isProp->PathP (\i -> isProp-≤)

      path : a == b
      path i = Iℚ-cons (pl i) (pu i) (p≤ i)

NonNegI : Pred Iℚ ℓ-zero
NonNegI a = 0# ≤ Iℚ.l a
NonPosI : Pred Iℚ ℓ-zero
NonPosI a = Iℚ.u a ≤ 0#
CrossZeroI : Pred Iℚ ℓ-zero
CrossZeroI a =  Iℚ.l a ≤ 0# × 0# ≤ Iℚ.u a

PosI : Pred Iℚ ℓ-zero
PosI a = 0# < Iℚ.l a
NegI : Pred Iℚ ℓ-zero
NegI a = Iℚ.u a < 0#
StrictCrossZeroI : Pred Iℚ ℓ-zero
StrictCrossZeroI a = Iℚ.l a < 0# × 0# < Iℚ.u a

ConstantI : Pred Iℚ ℓ-zero
ConstantI a = (Iℚ.l a) == (Iℚ.u a)

SymI : Pred Iℚ ℓ-zero
SymI a = (Iℚ.l a) == (- (Iℚ.u a))

ℚ∈Iℚ : ℚ -> Pred Iℚ ℓ-zero
ℚ∈Iℚ q a = (Iℚ.l a ≤ q) × (q ≤ Iℚ.u a)

NonConstantI : Pred Iℚ ℓ-zero
NonConstantI a = Iℚ.l a < Iℚ.u a

ZeroEndedI : Pred Iℚ ℓ-zero
ZeroEndedI a = (Iℚ.l a == 0#) ⊎ (Iℚ.u a == 0#)
