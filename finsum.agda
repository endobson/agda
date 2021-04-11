{-# OPTIONS --cubical --safe --exact-split #-}

module finsum where

open import base
open import equality
open import fin
open import functions
open import ring
open import ring.implementations

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {D : Type ℓ} (S : Semiring D) where
  open Semiring S

  finSumDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finSumDep zero    _ = 0#
  finSumDep (suc n) f = f zero-fin + (finSumDep n (f ∘ suc-fin))

  i<nSum : (n : Nat) -> (f : Nat -> D) -> D
  i<nSum n f = finSumDep n (\ (x , _) -> f x)

  enumerationSum : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationSum enum f = finSumDep _ (f ∘ enum)

i<nSum-zero : {n : Nat} -> i<nSum NatSemiring n (\i -> 0) == 0
i<nSum-zero {n = zero}  = refl
i<nSum-zero {n = suc n} = i<nSum-zero {n}

i<nSum-one : {n : Nat} -> i<nSum NatSemiring n (\i -> 1) == n
i<nSum-one {n = zero}  = refl
i<nSum-one {n = suc n} = cong suc (i<nSum-one {n})
