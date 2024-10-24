{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances.sum-triple where

open import base
open import equality
open import fin.sum-triple
open import fin.sum-pair
open import finset
open import finset.instances.sigma
open import finset.instances.sum-pair
open import isomorphism
open import univalence

opaque
  isFinSet-FinTriple+ : {n : Nat} -> isFinSet (FinTriple+ n)
  isFinSet-FinTriple+ {n} =
    subst isFinSet (isoToPath (iso⁻¹ FinTriple+-split₁)) isFinSet-TwoPair
    where
    TwoPair : Type₀
    TwoPair = Σ[ (fin-pair+ i jk _) ∈ FinPair+ n ] (FinPair+ jk)

    isFinSet-TwoPair : isFinSet TwoPair
    isFinSet-TwoPair =
      isFinSet-Σ isFinSet-FinPair+
                 (\(fin-pair+ i jk _) -> isFinSet-FinPair+)

  instance
    FinSetStr-FinTriple+ : {n : Nat} -> FinSetStr (FinTriple+ n)
    FinSetStr-FinTriple+ {n} = record { isFin = isFinSet-FinTriple+ }
