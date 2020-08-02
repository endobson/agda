{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2 where

open import base
open import div
open import equality
open import gcd
open import hlevel
open import int
open import nat
open import prime
open import prime-factorization
open import prime-gcd
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
  divisors-full : (n : Nat⁺) -> Σ (List Nat) (CanonicalList≥ (_div' ⟨ n ⟩))
  divisors-full n = list-reify (isBoundedDiv' n) (\d -> decide-div d ⟨ n ⟩)

  divisors : (n : Nat⁺) -> List Nat
  divisors n = fst (divisors-full n)

  divisors-canonical : (n : Nat⁺) -> (CanonicalList≥ (_div' ⟨ n ⟩) (divisors n))
  divisors-canonical n = (snd (divisors-full n))

  divisors-contains-only : (n : Nat⁺) -> (ContainsOnly (_div' ⟨ n ⟩) (divisors n))
  divisors-contains-only n = fst (fst (fst (snd (divisors-full n))))


module _ where
  private
    divisors-of-prime : (p : Prime') -> List Nat
    divisors-of-prime (p , _) = p :: 1 :: []

    divisors-of-prime-canonical :
      (p : Prime') -> CanonicalList≥ (_div' ⟨ p ⟩) (divisors-of-prime p)
    divisors-of-prime-canonical p@(p' , is-prime) = ((c-o , c-a) , nd) , sorted
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
      sorted : Sorted _≥_ (divisors-of-prime p)
      sorted = ((\{(0 , path) -> p≥a path}) , (\()) , lift tt)
        where
        p≥a : {a : Nat} -> (a == 1) -> p' ≥ a
        p≥a a==1 = transport (\i -> p' ≥ (a==1 (~ i))) (weaken-< (IsPrime'.>1 is-prime))

  prime-divisors-path : (p : Prime') -> divisors (Prime->Nat⁺ p) == (⟨ p ⟩ :: 1 :: [])
  prime-divisors-path p =
    canonical-list-== (divisors-canonical (Prime->Nat⁺ p)) (divisors-of-prime-canonical p)

-- Divisors of prime powers

prime-power : Prime' -> Nat -> Nat
prime-power (p , _) n = p ^' n

module _ (p : Prime') where
  private
    p' = fst p
    is-prime = snd p
    p-pos = IsPrime'.pos is-prime

    ¬p-divides->1 : (n : Nat) {d : Nat} -> d div' (prime-power p n)
                    -> ¬ (p' div' d) -> d == 1
    ¬p-divides->1 zero    {d} d%pn  _    = div'-one->one d%pn
    ¬p-divides->1 (suc n) {d} d%psn ¬d%p = ¬p-divides->1 n d%pn ¬d%p
      where
      d%pn : d div' (prime-power p n)
      d%pn = euclids-lemma' d%psn (gcd'-sym (prime->relatively-prime p ¬d%p))

    ¬p-divides->pn : (n x d : Nat) -> (x *' d == (prime-power p n))
                     -> ¬(p' div' x) -> d == (prime-power p n)
    ¬p-divides->pn n x d x-path ¬p%x =
      sym (*'-left-one {d}) >=> *'-left (sym x==1) >=> x-path
      where
      x==1 : x == 1
      x==1 = (¬p-divides->1 n (d , *'-commute {d} {x} >=> x-path) ¬p%x)


    p-divides->%pn : (n x d : Nat) -> (x *' d == (prime-power p (suc n)))
                     -> p' div' x -> d div' (prime-power p n)
    p-divides->%pn n x d x-path (z , z-path) =
      (z , *'-left-injective p-pos path)
      where
      path : p' *' (z *' d) == (prime-power p (suc n))
      path = sym (*'-assoc {p'} {z} {d})
             >=> *'-left (*'-commute {p'} {z} >=> z-path)
             >=> x-path

    split-prime-power-divisor :
      {n : Nat} {d : Nat} -> d div' (prime-power p (suc n))
      -> (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
    split-prime-power-divisor {n} {d} (x , x-path) =
      handle (decide-div p' x)
      where
      handle : (Dec (p' div' x)) -> (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
      handle (yes p%x) = inj-r (p-divides->%pn n x d x-path p%x)
      handle (no ¬p%x) = inj-l (¬p-divides->pn (suc n) x d x-path ¬p%x)



divisor-sum : (n : Nat⁺) -> (Σ[ d ∈ Nat ] (d div' ⟨ n ⟩) -> Int) -> Int
divisor-sum n f = Ring.sum IntRing (map f (contains-only->list (divisors n) (divisors-contains-only n)))
