{-# OPTIONS --cubical --safe --exact-split #-}

module type-algebra.boolean where

open import base
open import equality
open import equivalence.base
open import fin
open import isomorphism
open import nat

Fin2≃Boolean : Fin 2 ≃ Boolean
Fin2≃Boolean = (isoToEquiv i)
  where
  open Iso
  i : Iso (Fin 2) Boolean
  i .fun (zero  , _) = true
  i .fun (suc _ , _) = false
  i .inv true = zero-fin
  i .inv false = suc-fin zero-fin

  i .rightInv true = refl
  i .rightInv false = refl

  i .leftInv  (zero  , _)  = fin-i-path refl
  i .leftInv  (suc n , lt) = fin-i-path (cong suc (sym path))
    where
    path : n == 0
    path = zero-≤->zero (pred-≤ (pred-≤ lt))
