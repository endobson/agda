{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.triangular-numbers where

open import base
open import nat
open import combinatorics.binomial-coefficients

-- Zero indexed triangular numbers
triangular-number : Nat -> Nat
triangular-number zero = zero
triangular-number (suc n) = binomial-coeff' n 2
