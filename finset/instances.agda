{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances where

open import base
open import cubical
open import equivalence
open import fin
open import finset
open import fin-algebra
open import truncation

private
  isFinSet-Top : isFinSet Top
  isFinSet-Top = ∣ 1 , pathToEquiv (\i -> Fin-Top (~ i)) ∣

FinSet-Top : FinSet ℓ-zero
FinSet-Top = Top , isFinSet-Top

private
  isFinSet-Fin : {n : Nat} -> isFinSet (Fin n)
  isFinSet-Fin {n = n} = ∣ n , pathToEquiv (\i -> Fin n) ∣

FinSet-Fin : (n : Nat) -> FinSet ℓ-zero
FinSet-Fin n = Fin n , isFinSet-Fin
