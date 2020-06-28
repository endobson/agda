{-# OPTIONS --cubical --safe --exact-split #-}

module ind-permutation where

open import base
open import equality
open import equivalence
open import fin
open import functions
open import isomorphism
open import hlevel
open import nat
open import relation
open import sigma

open Iso

Perm : Nat -> Type₀
Perm n = Auto (FinInd n)

-- Identity permutation
idPerm : {n : Nat} -> Perm n
idPerm = id-iso

-- Permutation that holds 'zero-fin' constant and acts like the shifted argument otherwise
suc-fin-f : {n : Nat} -> (FinInd n -> FinInd n) -> (FinInd (suc n) -> FinInd (suc n))
suc-fin-f f (zero  , _          ) = zero-fin-ind
suc-fin-f f (suc i , (suc-≤i lt)) = suc-fin-ind (f (i , lt))

sucPerm : {n : Nat} -> Perm n -> Perm (suc n)
sucPerm φ .fun = suc-fin-f (φ .fun)
sucPerm φ .inv = suc-fin-f (φ .inv)
sucPerm φ .rightInv (zero  , (suc-≤i zero-≤i))   = refl
sucPerm φ .rightInv (suc i , (suc-≤i lt     )) j = suc-fin-ind (φ .rightInv (i , lt) j)
sucPerm φ .leftInv  (zero  , (suc-≤i zero-≤i))   = refl
sucPerm φ .leftInv  (suc i , (suc-≤i lt     )) j = suc-fin-ind (φ .leftInv (i , lt) j)
