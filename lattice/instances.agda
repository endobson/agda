{-# OPTIONS --cubical --safe --exact-split #-}

module lattice.instances where

open import base
open import div
open import gcd
open import lattice
open import lcm
open import lcm.exists
open import nat
open import relation
open import sigma


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

div# : RawLattice Nat⁺
RawLattice._≼_ div# = _div⁺_
RawLattice._∧_ div# = gcd⁺
RawLattice._∨_ div# = lcm⁺

instance
  open IsLattice
  open Supremum
  open Infimum

  isLattice-div : IsLattice div#
  isLattice-div .partial-order = (div'-trans , div'-refl , div⁺-antisym)
    where
    div⁺-antisym : {a b : Nat⁺} -> a div⁺ b -> b div⁺ a -> a == b
    div⁺-antisym d1%d2 d2%d1 = ΣProp-path isPropPos' (div'-antisym d1%d2 d2%d1)
  isLattice-div .supremum .x≼x∨y = \ a b -> LCM'.a%m (lcm⁺-proof a b)
  isLattice-div .supremum .y≼x∨y = \ a b -> LCM'.b%m (lcm⁺-proof a b)
  isLattice-div .supremum .∨-least = \ a b z -> LCM'.f (lcm⁺-proof a b) ⟨ z ⟩
  isLattice-div .infimum .x∧y≼x = \ a b -> GCD'.%a (gcd⁺-proof a b)
  isLattice-div .infimum .x∧y≼y = \ a b -> GCD'.%b (gcd⁺-proof a b)
  isLattice-div .infimum .∧-greatest = \ a b z -> GCD'.f (gcd⁺-proof a b) ⟨ z ⟩
