{-# OPTIONS --cubical --safe --exact-split #-}

module nat.properties where

open import base
open import equality
open import equivalence
open import hlevel
open import isomorphism
open import relation

Pos' : (n : Nat) -> Set
Pos' zero = Bot
Pos' (suc x) = Top

isPropPos' : {n : Nat} -> isProp (Pos' n)
isPropPos' {zero}  = isPropBot
isPropPos' {suc _} = isPropTop

Nat⁺ : Type₀
Nat⁺ = Σ[ n ∈ Nat ] (Pos' n)

zero-suc-absurd : {A : Set} {x : Nat} -> 0 == (suc x) -> A
zero-suc-absurd path = bot-elim (subst Pos' (sym path) tt)

-- Internal implementation of pred to avoid circularity issues
private
  pred : Nat -> Nat
  pred zero = zero
  pred (suc m) = m

suc-injective : {m n : Nat} -> suc m == suc n -> m == n
suc-injective p i = pred (p i)

decide-nat : (x : Nat) -> (y : Nat) -> Dec (x == y)
decide-nat zero zero = yes refl
decide-nat zero (suc n) = no (\ p -> zero-suc-absurd p)
decide-nat (suc m) zero = no (\ p -> zero-suc-absurd (sym p))
decide-nat (suc m) (suc n) with (decide-nat m n)
...  | (yes refl) = yes (cong suc refl)
...  | (no f) = no (\ pr -> f (suc-injective pr) )

discreteNat : Discrete Nat
discreteNat = decide-nat

isSetNat : isSet Nat
isSetNat = Discrete->isSet discreteNat

-- Lift suc up to path structure
private
  suc-iso : {m n : Nat} -> Iso (m == n) (suc m == suc n)
  Iso.fun suc-iso = cong suc
  Iso.inv suc-iso = cong pred
  Iso.rightInv suc-iso _ = isSet->Square isSetNat
  Iso.leftInv  suc-iso _ = isSet->Square isSetNat

suc-path : {m n : Nat} -> (m == n) == (suc m == suc n)
suc-path = ua (isoToEquiv suc-iso)
