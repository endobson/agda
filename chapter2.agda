{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2 where

open import base
open import chapter2.square-free
open import chapter2.divisors
open import commutative-monoid
open import div
open import equality
open import functions
open import hlevel
open import int
open import list
open import list.discrete
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
