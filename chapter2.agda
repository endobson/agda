{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2 where

open import base
open import div
open import equality
open import hlevel
open import int
open import nat
open import prime
open import prime-factorization
open import relation
open import ring
open import unique-prime-factorization
open import list
open import list.discrete
open import list.nat

import unordered-list as ul

private
  variable
    ℓ : Level
    A : Type ℓ

SquareFree : Nat⁺ -> Type₀
SquareFree (n , _) = (p : Prime') (pf : PrimeFactorization n)
                     -> ul.count p (PrimeFactorization.primes pf) ≤ 1

isPropSquareFree : {n : Nat⁺} -> isProp (SquareFree n)
isPropSquareFree = isPropΠ2 (\_ _ -> isProp≤)

private
  decide-SquareFree : (n : Nat⁺) -> Dec (SquareFree n)
  decide-SquareFree n⁺@(n@(suc _) , n-pos) = answer
    where
    pf : PrimeFactorization n
    pf = compute-prime-factorization zero-<

    no-dupes : Dec (ul.NoDuplicates (PrimeFactorization.primes pf))
    no-dupes = (ul.decide-no-duplicates (PrimeFactorization.primes pf))

    answer : Dec (SquareFree n⁺)
    answer with no-dupes
    ... | (yes f) = (yes g)
      where
      g : (p : Prime') (pf2 : PrimeFactorization n) -> ul.count p (PrimeFactorization.primes pf2) ≤ 1
      g p pf2 = transport (\i -> ul.count p (PrimeFactorization.primes (pf-path i)) ≤ 1) (f p)
        where
        pf-path : pf == pf2
        pf-path = isPropPrimeFactorization pf pf2
    ... | (no ¬f) = (no ¬g)
      where
      ¬g : ¬ ((p : Prime') (pf2 : PrimeFactorization n) -> ul.count p (PrimeFactorization.primes pf2) ≤ 1)
      ¬g g = ¬f (\p -> g p pf)


μ : Nat⁺ -> Int
μ n⁺@(n@(suc _) , n-pos) with (decide-SquareFree n⁺)
... | (yes _) = (neg zero) ^ (ul.length (PrimeFactorization.primes (compute-prime-factorization {n} zero-<)))
... | (no _)  = zero-int

isBoundedDiv' : (n : Nat⁺) -> isBounded (_div' ⟨ n ⟩)
isBoundedDiv' (n , pos-n) = (suc n) , (\p -> suc-≤ (div'->≤ p {pos-n}))

private
  divisors-full : (n : Nat⁺) -> Σ (List Nat) (ContainsExactlyOnce (_div' ⟨ n ⟩))
  divisors-full n = list-reify (isBoundedDiv' n) (\d -> decide-div d ⟨ n ⟩)

  divisors : (n : Nat⁺) -> List Nat
  divisors n = fst (divisors-full n)

  divisors-contains-only : (n : Nat⁺) -> (ContainsOnly (_div' ⟨ n ⟩) (divisors n))
  divisors-contains-only n = fst (fst (snd (divisors-full n)))

divisors-of-prime : (p : Prime') -> List Nat
divisors-of-prime (p , _) = p :: 1 :: []

divisors-of-prime-contains-exactly-once :
  (p : Prime') -> ContainsExactlyOnce (_div' ⟨ p ⟩) (divisors-of-prime p)
divisors-of-prime-contains-exactly-once p@(p' , is-prime)  = (c-o , c-a) , nd
  where
  c-o : ContainsOnly (_div' ⟨ p ⟩) (divisors-of-prime p)
  c-o (0 , path) = transport (cong (_div' p') (sym path)) div'-refl
  c-o (1 , path) = transport (cong (_div' p') (sym path)) div'-one
  c-a : ContainsAll (_div' ⟨ p ⟩) (divisors-of-prime p)
  c-a {d} dp = handle (prime-only-divisors p dp)
    where
    handle : (d == p' ⊎ d == 1) -> contains d (divisors-of-prime p)
    handle (inj-l path) = (0 , path)
    handle (inj-r path) = (1 , path)
  nd : NoDuplicates (divisors-of-prime p)
  nd = ((\{(0 , path) -> p!=1 path}) , (\()) , lift tt)
    where
    p!=1 : p' != 1
    p!=1 p==1 = <->!= (IsPrime'.>1 is-prime) (sym p==1)





divisor-sum : (n : Nat⁺) -> (Σ[ d ∈ Nat ] (d div' ⟨ n ⟩) -> Int) -> Int
divisor-sum n f = Ring.sum IntRing (map f (contains-only->list (divisors n) (divisors-contains-only n)))
