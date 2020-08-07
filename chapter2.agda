{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2 where

open import base
open import chapter2.square-free
open import commutative-monoid
open import div
open import equality
open import functions
open import gcd
open import hlevel
open import int
open import list
open import list.discrete
open import list.nat
open import list.sorted
open import nat
open import prime
open import prime-factorization
open import prime-gcd
open import relation
open import ring
open import ring.lists
open import ring.implementations
open import sigma
open import unique-prime-factorization


import unordered-list as ul

private
  variable
    ℓ : Level
    A : Type ℓ



μ : Nat⁺ -> Int
μ n⁺ with (decide-square-free n⁺)
... | (yes _) = (neg zero) ^ (ul.length (PrimeFactorization.primes (compute-prime-factorization n⁺)))
... | (no _)  = zero-int

μ⁰ : Nat -> Int
μ⁰ zero    = zero-int
μ⁰ (suc n) = μ ((suc n) , tt)

square-free-μ : {n : Nat⁺} -> SquareFree n -> (pf : PrimeFactorization ⟨ n ⟩)
               -> μ n == (neg zero) ^ (ul.length (PrimeFactorization.primes pf))
square-free-μ {n⁺} sf pf with (decide-square-free n⁺)
... | (yes _) = (\i -> (neg zero) ^ (ul.length (PrimeFactorization.primes (pf-path i))))
  where
  pf-path : (compute-prime-factorization n⁺) == pf
  pf-path = isPropPrimeFactorization _ _
... | (no ¬sf) = bot-elim (¬sf sf)


¬square-free-μ : {n : Nat⁺} -> ¬(SquareFree n) -> μ n == zero-int
¬square-free-μ {n⁺@(n@(suc _) , _)} ¬sf with (decide-square-free n⁺)
... | (yes sf) = bot-elim (¬sf sf)
... | (no _) = refl



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
  divisors-of-one : List Nat
  divisors-of-one = 1 :: []

  divisors-of-one-canonical : CanonicalList≥ (_div' 1) divisors-of-one
  divisors-of-one-canonical = ((c-o , c-a) , nd) , sorted
    where
    c-o : ContainsOnly (_div' 1) divisors-of-one
    c-o (0 , path) = transport (cong (_div' 1) (sym path)) div'-one
    c-a : ContainsAll (_div' 1) divisors-of-one
    c-a {d} (x , path) = (0 , (*'-only-one-right {x} {d} path))
    nd : NoDuplicates divisors-of-one
    nd = (\()) , lift tt
    sorted : Sorted _≥_ divisors-of-one
    sorted = (\()) , lift tt


  1⁺ : Nat⁺
  1⁺ = (1 , tt)

  one-divisors-path : divisors 1⁺ == 1 :: []
  one-divisors-path = canonical-list-== (divisors-canonical 1⁺) divisors-of-one-canonical


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
        p!=1 p==1 = <->!= (Prime'.>1 p) (sym p==1)
      sorted : Sorted _≥_ (divisors-of-prime p)
      sorted = ((\{(0 , path) -> p≥a path}) , (\()) , lift tt)
        where
        p≥a : {a : Nat} -> (a == 1) -> p' ≥ a
        p≥a a==1 = transport (\i -> p' ≥ (a==1 (~ i))) (weaken-< (Prime'.>1 p))

  prime-divisors-path : (p : Prime') -> divisors (Prime'.nat⁺ p) == (⟨ p ⟩ :: 1 :: [])
  prime-divisors-path p =
    canonical-list-== (divisors-canonical (Prime'.nat⁺ p)) (divisors-of-prime-canonical p)

-- Divisors of prime powers

module _ (p : Prime') where

  private
    p' = fst p
    is-prime = snd p
    p-pos = Prime'.pos p

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

  divisors-of-prime-power : Nat -> List Nat
  divisors-of-prime-power zero       = 1 :: []
  divisors-of-prime-power n@(suc n') = (p' ^' n) :: (divisors-of-prime-power n')

  private
    contains-only-divisors-of-prime-power : (n : Nat) ->
      ContainsOnly (_div' (p' ^' n)) (divisors-of-prime-power n)
    contains-only-divisors-of-prime-power zero    (0 , path) =
      (1 , *'-left-one >=> path)
    contains-only-divisors-of-prime-power (suc n) (0 , path) =
      (1 , *'-left-one >=> path)
    contains-only-divisors-of-prime-power (suc n) (suc i , path) =
      div'-mult (contains-only-divisors-of-prime-power n (i , path)) p'

    sorted>-divisors-of-prime-power : (n : Nat) -> Sorted _>_ (divisors-of-prime-power n)
    sorted>-divisors-of-prime-power zero = sorted-singleton _>_ 1
    sorted>-divisors-of-prime-power (suc n) =
      (>all , sorted>-divisors-of-prime-power n)
      where
      >all : ContainsOnly (_< (p' *' (p' ^' n))) (divisors-of-prime-power n)
      >all {x} c = trans-≤-< x-lt p-lt
        where
        x-div : x div' (p' ^' n)
        x-div = contains-only-divisors-of-prime-power n c
        x-lt : x ≤ (p' ^' n)
        x-lt = div'->≤ x-div {^'-Pos' (Prime'.pos p) n}
        p-lt : (p' ^' n) < (p' ^' (suc n))
        p-lt = ^-suc-< (Prime'.>1 p) n


  divisors-of-prime-power-canonical :
    (n : Nat) -> CanonicalList≥ (_div' (p' ^' n)) (divisors-of-prime-power n)
  divisors-of-prime-power-canonical zero = divisors-of-one-canonical
  divisors-of-prime-power-canonical (suc n) = ((c-o , c-a) , nd) , sorted
    where
    c-o = contains-only-divisors-of-prime-power (suc n)
    c-a : ContainsAll (_div' (p' *' (p' ^' n))) (divisors-of-prime-power (suc n))
    c-a {d} dp = handle (split-prime-power-divisor {n} {d} dp)
      where
      handle : (d == (⟨ p ⟩ *' (⟨ p ⟩ ^' n)) ⊎ d div' (⟨ p ⟩ ^' n))
               -> contains d (divisors-of-prime-power (suc n))
      handle (inj-l path) = (0 , path)
      handle (inj-r rec) =
        cons-contains (⟨ p ⟩ *' (⟨ p ⟩ ^' n))
                      (canonical-contains-all (divisors-of-prime-power-canonical n) rec)

    nd : NoDuplicates (divisors-of-prime-power (suc n))
    nd = sorted>->no-duplicates (sorted>-divisors-of-prime-power (suc n))
    sorted : Sorted _≥_ (divisors-of-prime-power (suc n))
    sorted = sorted>->sorted≥ (sorted>-divisors-of-prime-power (suc n))


μ1==1 : μ⁰ 1 == (int 1)
μ1==1 = refl

μp==-1 : (p : Prime') -> μ (Prime'.nat⁺ p) == (- (int 1))
μp==-1 p = square-free-μ (prime-square-free p) (prime-prime-factorization p)

relatively-prime-μ : {a b : Nat⁺} -> RelativelyPrime' ⟨ a ⟩ ⟨ b ⟩
                     -> μ (a *⁺ b) == μ a * μ b
relatively-prime-μ {a} {b} rp = handle (decide-square-free a) (decide-square-free b)
  where
  handle : Dec (SquareFree a) -> Dec (SquareFree b) -> μ (a *⁺ b) == μ a * μ b
  handle _ (no ¬sf-b) =
    begin
      μ (a *⁺ b)
    ==< ¬square-free-μ (¬square-free-*-right a {b} ¬sf-b) >
      (int 0)
    ==< sym (*-right-zero {μ a}) >
      μ a * (int 0)
    ==< *-right {μ a} (sym (¬square-free-μ ¬sf-b)) >
      μ a * μ b
    end
  handle (yes sf-a) (yes sf-b) =
    begin
      μ (a *⁺ b)
    ==< square-free-μ sf-ab pf-ab >
      (- (int 1)) ^ (ul.length (primes-a ul.++ primes-b))
    ==< CommMonoidʰ.preserves-∙ (^ʰ (- (int 1)) ∘ʰ ul.lengthʰ) primes-a primes-b >
      (- (int 1)) ^ (ul.length primes-a) * (- (int 1)) ^ (ul.length primes-b)
    ==< *-left (sym (square-free-μ sf-a pf-a)) >
      μ a * (- (int 1)) ^ (ul.length primes-b)
    ==< *-right {μ a} (sym (square-free-μ sf-b pf-b)) >
      μ a * μ b
    end
    where
    pf-a = compute-prime-factorization a
    pf-b = compute-prime-factorization b
    pf-ab = *'-prime-factorization pf-a pf-b

    primes-a = PrimeFactorization.primes pf-a
    primes-b = PrimeFactorization.primes pf-b

    sf-ab : SquareFree (a *⁺ b)
    sf-ab = relatively-prime-square-free a b rp sf-a sf-b
  handle (no ¬sf-a) (yes sf-b) =
    begin
      μ (a *⁺ b)
    ==< ¬square-free-μ (¬square-free-*-left {a} ¬sf-a b) >
      (int 0)
    ==<>
      (int 0) * μ b
    ==< *-left (sym (¬square-free-μ ¬sf-a)) >
      μ a * μ b
    end


divisor-sum : (n : Nat⁺) -> (Σ[ d ∈ Nat ] (d div' ⟨ n ⟩) -> Int) -> Int
divisor-sum n f = sum IntSemiring (map f (contains-only->list (divisors n) (divisors-contains-only n)))
