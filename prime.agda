{-# OPTIONS --cubical --safe --exact-split #-}

module prime where

open import base
open import div
open import equality
open import nat

data IsPrime' : Nat -> Type₀ where
  is-prime' : (p' : Nat)
              -> ((d : Nat) -> d <s (suc (suc p')) -> (d div' (suc (suc p'))) -> d == 1)
              -> IsPrime' (suc (suc p'))

record Prime' : Type₀ where
  field
    value : Nat
    proof : IsPrime' value


prime-only-divisors : {p d : Nat} -> IsPrime' p -> d div' p -> (d == p) ⊎ (d == 1)
prime-only-divisors {p} {d} (is-prime' _ pf) d%p with (≤->≤s (div'->≤ d%p))
... | refl-≤s = inj-l refl
... | (step-≤s pr) = inj-r (pf d (inc-≤s pr) d%p)

-- Machinery for proving that a number is Prime
module PrimeUpTo where
  data PrimeUpTo : Nat -> Nat -> Type₀ where
    prime-up-to : (p' : Nat) -> (bound : Nat)
                  -> ((d : Nat) -> d <s bound -> (d div' (suc (suc p'))) -> d == 1)
                  -> PrimeUpTo (suc (suc p')) bound

  prime-up-to->is-prime' : {n : Nat} -> PrimeUpTo n n -> IsPrime' n
  prime-up-to->is-prime' (prime-up-to p' (suc (suc p')) f) = (is-prime' p' f)

  prime-up-to-zero : (p' : Nat) -> PrimeUpTo (suc (suc p')) zero
  prime-up-to-zero p' = prime-up-to p' zero (\ d ())

  prime-up-to-suc : {p b : Nat} -> PrimeUpTo p b -> ¬(b div' p) -> PrimeUpTo p (suc b)
  prime-up-to-suc {p} (prime-up-to p' b f) ¬bp = (prime-up-to p' (suc b) g)
    where
    g : (d : Nat) -> d <s (suc b) -> (d div' p) -> d == 1
    g d refl-≤s dp = bot-elim (¬bp dp)
    g d (step-≤s d≤b) dp = f d d≤b dp

  prime-up-to-one : (p' : Nat) -> PrimeUpTo (suc (suc p')) 1
  prime-up-to-one p' = prime-up-to-suc (prime-up-to-zero p') pr
    where
    pr : ¬(0 div' (suc (suc p')))
    pr 0p = zero-suc-absurd (sym (div'-zero->zero 0p))

  prime-up-to-two : (p' : Nat) -> PrimeUpTo (suc (suc p')) 2
  prime-up-to-two p' = prime-up-to p' 2 g
    where
    g : (d : Nat) -> d <s 2 -> (d div' (suc (suc p'))) -> d == 1
    g d refl-≤s dp = refl
    g d (step-≤s d≤b) dp with (prime-up-to-one p')
    ... | (prime-up-to _ _ f) = f d d≤b dp

open PrimeUpTo

0-is-¬prime : ¬(IsPrime' 0)
0-is-¬prime ()
1-is-¬prime : ¬(IsPrime' 1)
1-is-¬prime ()
2-is-prime : IsPrime' 2
2-is-prime = prime-up-to->is-prime' (prime-up-to-two 0)
