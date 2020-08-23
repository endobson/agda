{-# OPTIONS --cubical --safe --exact-split #-}

module prime-div-count.computational where

open import base
open import div
open import nat
open import prime
open import prime-div-count
open import gcd.computational
open import lcm.exists

prime-div-count : Prime' -> Nat⁺ -> Nat
prime-div-count p a = fst (compute-prime-div-count p a)
prime-div-count-proof : (p : Prime') -> (a : Nat⁺) -> PrimeDivCount p ⟨ a ⟩ (prime-div-count p a)
prime-div-count-proof p a = snd (compute-prime-div-count p a)

*'-prime-div-count⁺ : (p : Prime') (a b : Nat⁺)
  -> prime-div-count p (a *⁺ b) == prime-div-count p a +' prime-div-count p b
*'-prime-div-count⁺ p a b =
  prime-div-count-unique
    (prime-div-count-proof p (a *⁺ b))
    (*'-prime-div-count (prime-div-count-proof p a) (prime-div-count-proof p b))

div-prime-div-count : {a b : Nat⁺} -> a div⁺ b -> (p : Prime')
                      -> prime-div-count p a ≤ prime-div-count p b
div-prime-div-count {a} {b} a%b p = handle (split-nat< nb na)
  where
  na = prime-div-count p a
  nb = prime-div-count p b
  handle : (nb < na ⊎ na ≤ nb) -> na ≤ nb
  handle (inj-r lt) = lt
  handle (inj-l lt) =
    bot-elim (PrimeDivCount.¬p^sn%a (prime-div-count-proof p b)
               (div'-trans (div'-trans (div'-^' lt) (PrimeDivCount.%a (prime-div-count-proof p a)))
                            a%b))

gcd-prime-div-count⁺ : (p : Prime') (a b : Nat⁺)
  -> prime-div-count p (gcd⁺ a b) == min (prime-div-count p a) (prime-div-count p b)
gcd-prime-div-count⁺ p a b =
  prime-div-count-unique
    (prime-div-count-proof p (gcd⁺ a b))
    (gcd-prime-div-count (gcd⁺-proof a b) p (prime-div-count-proof p a) (prime-div-count-proof p b))

lcm-prime-div-count⁺ : (p : Prime') (a b : Nat⁺)
  -> prime-div-count p (lcm⁺ a b) == max (prime-div-count p a) (prime-div-count p b)
lcm-prime-div-count⁺ p a b =
  (prime-div-count-unique
    (prime-div-count-proof p (lcm⁺ a b))
    (lcm-prime-div-count (lcm⁺-proof a b) p (prime-div-count-proof p a) (prime-div-count-proof p b)))
