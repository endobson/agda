{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.unordered-divisors where

open import base
open import nat
open import prime-factorization
open import unique-prime-factorization
open import unordered-list.base
open import unordered-list.operations
open import unordered-list.powerset

divisors : (n : Nat⁺) -> UList Nat
divisors n =
  map prime-product (powerset (PrimeFactorization.primes (compute-prime-factorization n)))
