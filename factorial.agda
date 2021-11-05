{-# OPTIONS --cubical --safe --exact-split #-}

module factorial where

open import base
open import nat
open import ring.implementations
open import semiring

factorial : ℕ -> ℕ
factorial zero = 1#
factorial (suc n) = (suc n) * factorial n
