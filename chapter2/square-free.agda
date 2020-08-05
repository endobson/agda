{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.square-free where

open import base
open import equality
open import functions
open import hlevel
open import nat
open import prime
open import prime-factorization
open import relation
open import sigma
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

prime-square-free : (p : Prime') -> SquareFree (Prime'.nat⁺ p)
prime-square-free p@(p' , _) p2@(p2' , _) pf = handle (decide-nat p2' p')
  where
  pf-path : pf == (prime-prime-factorization p)
  pf-path = isPropPrimeFactorization _ _

  handle : Dec (p2' == p') -> count p2 (PrimeFactorization.primes pf) ≤ 1
  handle (yes p'-path) = (0 , full-path)
    where
    p-path : p2 == p
    p-path = ΣProp-path isPropIsPrime' p'-path

    full-path : count p2 (PrimeFactorization.primes pf) == 1
    full-path =
      (\i -> count p2 (PrimeFactorization.primes (pf-path i)))
      >=> count-== [] p-path

  handle (no ¬path) = (1 , cong suc full-path)
    where
    ¬p-path : p2 != p
    ¬p-path = ¬path ∘ (cong fst)

    full-path : count p2 (PrimeFactorization.primes pf) == 0
    full-path =
      (\i -> count p2 (PrimeFactorization.primes (pf-path i)))
      >=> count-!= [] ¬p-path

prime-power-¬square-free : {n : Nat} (p : Prime') -> n ≥ 2 ->
                           ¬ (SquareFree (prime-power⁺ p n))
prime-power-¬square-free {zero}        p n≥2 sf = zero-≮ n≥2
prime-power-¬square-free {suc zero}    p n≥2 sf = zero-≮ (pred-≤ n≥2)
prime-power-¬square-free {suc (suc n)} p n≥2 sf =
  (same-≮ (trans-≤ p-count-≤ sf-≤))
  where
  primes-base : UList Prime'
  primes-base = (PrimeFactorization.primes (prime-power-prime-factorization p n))

  primes' : UList Prime'
  primes' = (p :: (p :: primes-base))

  sf-≤ : count p primes' ≤ 1
  sf-≤ = sf p (prime-power-prime-factorization p (suc (suc n)))

  p-count-≤ : 2 ≤ count p primes'
  p-count-≤ = count p primes-base ,
    (+'-commute {count p primes-base} {2})
    >=> cong suc (sym (count-== primes-base refl))
    >=> sym (count-== (p :: primes-base) refl)
