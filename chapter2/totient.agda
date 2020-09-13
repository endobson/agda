{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.totient where

open import base
open import equality
open import gcd.computational
open import gcd.propositional hiding (gcd'-unique)
open import list
open import list.nat
open import nat
open import prime-gcd
open import relatively-prime
open import relation

private
  record Totient (n : Nat) (k : Nat) : Type₀ where
    field
      k≤n : k ≤ n
      rp : RelativelyPrime⁰ k n

  isBoundedTotient : {n : Nat} -> isBounded (Totient n)
  isBoundedTotient {n} = (suc n) , (\ t -> trans-≤-< (Totient.k≤n t) (suc-≤ (same-≤ n)))

  decide-rp : (k n : Nat) -> Dec (RelativelyPrime⁰ k n)
  decide-rp k n = handle (decide-nat (gcd' k n) 1)
    where
    handle : Dec ((gcd' k n) == 1) -> Dec (RelativelyPrime⁰ k n)
    handle (no ¬p) = no (\ rp -> ¬p (gcd'-unique (relatively-prime->gcd rp)))
    handle (yes p) = yes (gcd->relatively-prime (transport (cong (GCD' k n) p) (gcd'-proof k n)))


  decide-totient : (n k : Nat) -> Dec (Totient n k)
  decide-totient n k = handle (decide-nat≤ k n) (decide-rp k n)
    where
    handle : Dec (k ≤ n) -> Dec (RelativelyPrime⁰ k n) -> Dec (Totient n k)
    handle (no ¬k≤n) _        = no (\ t -> ¬k≤n (Totient.k≤n t))
    handle (yes k≤n) (no ¬rp) = no (\ t -> ¬rp (Totient.rp t))
    handle (yes k≤n) (yes rp) = yes (record { k≤n = k≤n ; rp = rp })

  totient-full : (n : Nat) -> Σ (List Nat) (CanonicalList≥ (Totient n))
  totient-full n = list-reify isBoundedTotient (\ k -> decide-totient n k)

totient⁰ : (n : Nat) -> Nat
totient⁰ n = length (⟨ totient-full n ⟩)

totient : (n : Nat⁺) -> Nat
totient (n , _) = (totient⁰ n)
