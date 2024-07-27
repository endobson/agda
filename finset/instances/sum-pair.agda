{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances.sum-pair where

open import base
open import equality
open import fin
open import fin.sum-pair
open import finset
open import isomorphism
open import nat
open import nat.order
open import truncation

opaque
  isFinSet-FinPair+ : {n : Nat} -> isFinSet (FinPair+ n)
  isFinSet-FinPair+ {n} = ∣ (suc n) , isoToEquiv fin-iso ∣
    where
    fin-iso : Iso (FinPair+ n) (Fin (suc n))
    fin-iso .Iso.fun (fin-pair+ i j p) = j , suc-≤ (i , p)
    fin-iso .Iso.inv (j , i , p) =
      fin-pair+ i j (cong pred (sym +'-right-suc >=> p))
    fin-iso .Iso.leftInv (fin-pair+ i j p) =
      FinPair+-path refl refl
    fin-iso .Iso.rightInv (j , i , p) = fin-i-path refl


  instance
    FinSetStr-FinPair+ : {n : Nat} -> FinSetStr (FinPair+ n)
    FinSetStr-FinPair+ {n} = record { isFin = isFinSet-FinPair+ }
