{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.nth-root.base where

open import base
open import real
open import ring.implementations.real
open import semiring.exponentiation

isNthRoot : (n : Nat) (x : ℝ) (y : ℝ) -> Type₁
isNthRoot n x y = y ^ℕ n == x
