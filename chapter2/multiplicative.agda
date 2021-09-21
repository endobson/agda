{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.multiplicative where

open import additive-group using (AdditiveCommMonoid)
open import base
open import int hiding (_*_)
open import functions
open import nat
open import rational
open import relatively-prime
open import semiring

private
  variable
    ℓ : Level

record Multiplication {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    mult : Domain -> Domain -> Domain
    1# : Domain

instance
  NatMultiplication : Multiplication Nat
  NatMultiplication = record { mult = _*'_; 1# = 1 }

  Nat⁺Multiplication : Multiplication Nat⁺
  Nat⁺Multiplication = record { mult = _*⁺_; 1# = 1⁺ }

  IntMultiplication : Multiplication Int
  IntMultiplication = record { mult = int._*_; 1# = (int 1) }

  RationalMultiplication : Multiplication Rational
  RationalMultiplication = record { mult = _r*_; 1# = (ℕ->ℚ 1) }

SemiringMultiplication : {D : Type ℓ} -> {ACM : AdditiveCommMonoid D} ->
                         (S : Semiring ACM) -> Multiplication D
SemiringMultiplication S = record { mult = Semiring._*_ S ; 1# = Semiring.1# S }


Multiplicative : {D : Type ℓ} {{M : Multiplication D}} (f : Nat⁺ -> D) -> Type ℓ
Multiplicative {{M = M}} f =
  (f 1⁺ == Multiplication.1# M) ×
  ((a b : Nat⁺) -> (RelativelyPrime⁺ a b) ->
   f (a *⁺ b) == (Multiplication.mult M (f a) (f b)))

-- CompletelyMultiplicative : {D : Type ℓ} {{M : Multiplication D}} (f : Nat⁺ -> D) -> Type ℓ
-- CompletelyMultiplicative {{M = M}} f = (a b : Nat⁺) ->
--                                        f (a *⁺ b) == (Multiplication.mult M (f a) (f b))

Multiplicative⁰ : {D : Type ℓ} {{M : Multiplication D}} (f : Nat -> D) -> Type ℓ
Multiplicative⁰ {{M = M}} f =
  (f 1 == Multiplication.1# M) ×
  ((a b : Nat) -> (RelativelyPrime⁰ a b) ->
   f (a *' b) == (Multiplication.mult M (f a) (f b)))

-- Multiplicative⁰->⁺ : {D : Type ℓ} {{M : Multiplication D}} {f : Nat -> D} ->
--                      Multiplicative⁰ f -> Multiplicative (f ∘ fst)
-- Multiplicative⁰->⁺ m (a , _) (b , _) rp = m a b rp
