{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.square-free where

open import base
open import equality
open import hlevel
open import nat
open import prime
open import prime-factorization
open import relation
open import unique-prime-factorization
open import unordered-list

SquareFree : Nat⁺ -> Type₀
SquareFree (n , _) = (p : Prime') (pf : PrimeFactorization n)
                     -> count p (PrimeFactorization.primes pf) ≤ 1

SquareFree⁰ : Nat -> Type₀
SquareFree⁰ zero = Bot
SquareFree⁰ (suc n) = SquareFree ((suc n) , tt)


isPropSquareFree : {n : Nat⁺} -> isProp (SquareFree n)
isPropSquareFree = isPropΠ2 (\_ _ -> isProp≤)

decide-square-free : (n : Nat⁺) -> Dec (SquareFree n)
decide-square-free n⁺@(n@(suc _) , n-pos) = answer
  where
  pf : PrimeFactorization n
  pf = compute-prime-factorization n⁺

  no-dupes : Dec (NoDuplicates (PrimeFactorization.primes pf))
  no-dupes = (decide-no-duplicates (PrimeFactorization.primes pf))

  answer : Dec (SquareFree n⁺)
  answer with no-dupes
  ... | (yes f) = (yes g)
    where
    g : (p : Prime') (pf2 : PrimeFactorization n) -> count p (PrimeFactorization.primes pf2) ≤ 1
    g p pf2 = transport (\i -> count p (PrimeFactorization.primes (pf-path i)) ≤ 1) (f p)
      where
      pf-path : pf == pf2
      pf-path = isPropPrimeFactorization pf pf2
  ... | (no ¬f) = (no ¬g)
    where
    ¬g : ¬ ((p : Prime') (pf2 : PrimeFactorization n) -> count p (PrimeFactorization.primes pf2) ≤ 1)
    ¬g g = ¬f (\p -> g p pf)
