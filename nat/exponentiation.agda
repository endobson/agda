{-# OPTIONS --cubical --safe --exact-split #-}

module nat.exponentiation where

open import base
open import nat.arithmetic
open import nat.properties
open import semiring.instances.nat
open import semiring.exponentiation

private
  ^ℕ-Pos' : {a : Nat} -> .(Pos' a) -> (b : Nat) -> Pos' (a ^ℕ b)
  ^ℕ-Pos' _ zero = tt
  ^ℕ-Pos' p (suc n) = *'-Pos'-Pos' p (^ℕ-Pos' p n)

_^⁺_ : Nat⁺ -> Nat -> Nat⁺
(a , pos-a) ^⁺ b = a ^ℕ b , ^ℕ-Pos' pos-a b
