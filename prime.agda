{-# OPTIONS --cubical --safe --exact-split #-}

module prime where

open import base
open import div
open import equality
open import functions
open import hlevel
open import nat
open import relation
open import sigma

data IsPrime' : Nat -> Type₀ where
  is-prime' : (p : Nat)
              -> p > 1
              -> ((d : Nat) -> d <s p -> (d div' p) -> d == 1)
              -> IsPrime' p

isPropIsPrime' : {n : Nat} -> isProp (IsPrime' n)
isPropIsPrime' (is-prime' p gt1 f1) (is-prime' p gt2 f2) i =
  (is-prime' p (isProp≤ gt1 gt2 i) (isPropΠ3 (\ _ _ _ -> (isSetNat _ _)) f1 f2 i))

Prime' : Type₀
Prime' = Σ Nat IsPrime'

discretePrime' : Discrete Prime'
discretePrime' p1 p2 with (decide-nat ⟨ p1 ⟩ ⟨ p2 ⟩)
... | (yes pr) = yes (ΣProp-path isPropIsPrime' pr)
... | (no f) = no (f ∘ cong fst)

prime-only-divisors : {p d : Nat} -> IsPrime' p -> d div' p -> (d == p) ⊎ (d == 1)
prime-only-divisors {d = d} (is-prime' p p>1 pf) d%p with (≤->≤s (div'->≤ d%p {<->Pos' p>1}))
... | refl-≤s = inj-l refl
... | (step-≤s pr) = inj-r (pf d (suc-≤s pr) d%p)

-- Machinery for proving that a number is Prime
module PrimeUpTo where
  data PrimeUpTo : Nat -> Nat -> Type₀ where
    prime-up-to : (p : Nat) -> (bound : Nat)
                  -> p > 1
                  -> ((d : Nat) -> d <s bound -> (d div' p) -> d == 1)
                  -> PrimeUpTo p bound

  prime-up-to->is-prime' : {n : Nat} -> PrimeUpTo n n -> IsPrime' n
  prime-up-to->is-prime' (prime-up-to p p p>1 f) = (is-prime' p p>1 f)

  prime-up-to-zero : (p : Nat) -> (p > 1) -> PrimeUpTo p zero
  prime-up-to-zero p p>1 = prime-up-to p zero p>1 (\ d ())

  prime-up-to-suc : {p b : Nat} -> PrimeUpTo p b -> ¬(b div' p) -> PrimeUpTo p (suc b)
  prime-up-to-suc (prime-up-to p b lt f) ¬bp = (prime-up-to p (suc b) lt g)
    where
    g : (d : Nat) -> d <s (suc b) -> (d div' p) -> d == 1
    g d refl-≤s dp = bot-elim (¬bp dp)
    g d (step-≤s d≤b) dp = f d d≤b dp

  prime-up-to-one : (p : Nat) -> (p > 1) -> PrimeUpTo p 1
  prime-up-to-one p p>1 = prime-up-to-suc (prime-up-to-zero p p>1) pr
    where
    pr : ¬(0 div' p)
    pr 0p = zero-≮ (transport (\i -> (div'-zero->zero 0p i) > 1) p>1)

  prime-up-to-two : (p : Nat) -> (p > 1) -> PrimeUpTo p 2
  prime-up-to-two p p>1 = prime-up-to p 2 p>1 g
    where
    g : (d : Nat) -> d <s 2 -> (d div' p) -> d == 1
    g d refl-≤s dp = refl
    g d (step-≤s d≤b) dp with (prime-up-to-one p p>1)
    ... | (prime-up-to _ _ _ f) = f d d≤b dp

open PrimeUpTo

0-is-¬prime : ¬(IsPrime' 0)
0-is-¬prime (is-prime' _ lt _) = zero-≮ lt
1-is-¬prime : ¬(IsPrime' 1)
1-is-¬prime (is-prime' _ lt _) = zero-≮ (pred-≤ lt)
2-is-prime : IsPrime' 2
2-is-prime = prime-up-to->is-prime' (prime-up-to-two 2 (same-≤ 2))
