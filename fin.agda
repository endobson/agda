{-# OPTIONS --cubical --safe --exact-split #-}

module fin where

open import base
open import equality
open import nat

data Fin : Nat -> Set where
 zero-fin : {n : Nat} -> Fin (suc n)
 suc-fin : {n : Nat} -> Fin n -> Fin (suc n)

fin->nat : {n : Nat} -> Fin n -> Nat
fin->nat zero-fin = zero
fin->nat (suc-fin f) = suc (fin->nat f)

fin->nat-injective : {n : Nat} {x y : Fin n} -> (fin->nat x) == (fin->nat y) -> x == y
fin->nat-injective {_} {zero-fin} {zero-fin} _ = refl
fin->nat-injective {_} {suc-fin x} {suc-fin y} pr =
  (cong suc-fin (fin->nat-injective (suc-injective pr)))
fin->nat-injective {_} {zero-fin} {suc-fin _} pr = bot-elim (zero-suc-absurd pr)
fin->nat-injective {_} {suc-fin _} {zero-fin} pr = bot-elim (zero-suc-absurd (sym pr))

nat->fin : (n : Nat) -> Fin (suc n)
nat->fin zero = zero-fin
nat->fin (suc n) = suc-fin (nat->fin n)
