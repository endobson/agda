{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.id-function where

open import additive-group.instances.nat
open import additive-group.instances.int
open import base
open import nat
open import rational
open import finite-product
open import chapter2.multiplicative
open import chapter2.prime-divisors
open import ring.implementations.rational
open import ring.implementations
open import ring
open import prime
open import prime-div-count.computational

N : Nat⁺ -> Nat⁺
N x = x

N⁰ : Nat⁺ -> Nat
N⁰ (x , _) = x

Nℚ : Nat⁺ -> Rational
Nℚ (x , _) = ℕ->ℚ x

Multiplicative-N : Multiplicative N
Multiplicative-N .fst = refl
Multiplicative-N .snd _ _ _ = refl

Multiplicative-N⁰ : Multiplicative N⁰
Multiplicative-N⁰ .fst = refl
Multiplicative-N⁰ .snd _ _ _ = refl

Multiplicative-Nℚ : Multiplicative Nℚ
Multiplicative-Nℚ .fst = refl
Multiplicative-Nℚ .snd (a , _) (b , _) rp = Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ a b


finiteProduct-PrimeDivisor-N⁰ :
  (n : Nat⁺) ->
  ⟨ n ⟩ == finiteProduct (FinSet-PrimeDivisor n) (\(p , _) -> (prime-power p (prime-div-count p n)))
finiteProduct-PrimeDivisor-N⁰ n = Multiplicative-PrimeDivisor Multiplicative-N⁰
