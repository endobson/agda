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

record IsPrime' (p : Nat) : Type₀ where
  constructor is-prime'

  field
    >1 : p > 1
    only-one-divides : (d : Nat) -> d <s p -> (d div' p) -> d == 1

  pos : Pos' p
  pos = handle >1
    where
    handle : p > 1 -> Pos' p
    handle (n , path) = transport (cong Pos' (sym +'-right-suc >=> path)) tt

isPropIsPrime' : {n : Nat} -> isProp (IsPrime' n)
isPropIsPrime' (is-prime' gt1 f1) (is-prime' gt2 f2) i =
  (is-prime' (isProp≤ gt1 gt2 i) (isPropΠ3 (\ _ _ _ -> (isSetNat _ _)) f1 f2 i))

Prime' : Type₀
Prime' = Σ Nat IsPrime'

module Prime' (p : Prime') where
  private
    p' = ⟨ p ⟩
    is-prime = snd p

  pos : Pos' p'
  pos = IsPrime'.pos is-prime

  >1 : p' > 1
  >1 = IsPrime'.>1 is-prime

  !=1 : p' != 1
  !=1 = (<->!= >1) ∘ sym

  nat⁺ : Nat⁺
  nat⁺ = p' , pos


discretePrime' : Discrete Prime'
discretePrime' p1 p2 with (decide-nat ⟨ p1 ⟩ ⟨ p2 ⟩)
... | (yes pr) = yes (ΣProp-path isPropIsPrime' pr)
... | (no f) = no (f ∘ cong fst)

instance
  discrete'Prime' : Discrete' Prime'
  discrete'Prime' = record { f = discretePrime' }

prime-only-divisors : {d : Nat} -> (p : Prime') -> d div' ⟨ p ⟩ -> (d == ⟨ p ⟩) ⊎ (d == 1)
prime-only-divisors {d = d} (_ , (is-prime' p>1 pf)) d%p with (≤->≤s (div'->≤ d%p {<->Pos' p>1}))
... | refl-≤s = inj-l refl
... | (step-≤s pr) = inj-r (pf d (suc-≤s pr) d%p)

distinct-primes->¬div : {p1 p2 : Prime'} -> p1 != p2 -> ¬ (⟨ p1 ⟩ div' ⟨ p2 ⟩)
distinct-primes->¬div {p1@(_ , (is-prime' p1>1 _))} {p2} ¬path p1%p2
  with (prime-only-divisors p2 p1%p2)
... | inj-l p1==p2 = ¬path (ΣProp-path isPropIsPrime' p1==p2)
... | inj-r p1==1 = <->!= p1>1 (sym p1==1)

-- Machinery for proving that a number is Prime
module PrimeUpTo where
  data PrimeUpTo : Nat -> Nat -> Type₀ where
    prime-up-to : (p : Nat) -> (bound : Nat)
                  -> p > 1
                  -> ((d : Nat) -> d <s bound -> (d div' p) -> d == 1)
                  -> PrimeUpTo p bound

  prime-up-to->is-prime' : {n : Nat} -> PrimeUpTo n n -> IsPrime' n
  prime-up-to->is-prime' (prime-up-to p p p>1 f) = (is-prime' p>1 f)

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
0-is-¬prime (is-prime' lt _) = zero-≮ lt
1-is-¬prime : ¬(IsPrime' 1)
1-is-¬prime (is-prime' lt _) = zero-≮ (pred-≤ lt)
2-is-prime : IsPrime' 2
2-is-prime = prime-up-to->is-prime' (prime-up-to-two 2 (same-≤ 2))


-- Prime powers

prime-power : Prime' -> Nat -> Nat
prime-power (p , _) n = p ^' n

prime-power⁺ : Prime' -> Nat -> Nat⁺
prime-power⁺ p n = (prime-power p n , ^'-Pos' (Prime'.pos p) n)
