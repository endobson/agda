{-# OPTIONS --cubical --safe --exact-split #-}

module nat where

open import base
open import equality
open import hlevel
open import relation

open import nat.arithmetic public
open import nat.order public

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
