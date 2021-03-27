{-# OPTIONS --cubical --safe --exact-split #-}

module finsum where

open import base
open import equality
open import fin
open import functions
open import ring
open import ring.implementations
open import swap-permutation

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {D : Type ℓ} (S : Semiring D) where
  open Semiring S

  finSumDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finSumDep zero    _ = 0#
  finSumDep (suc n) f = f zero-fin + (finSumDep n (f ∘ suc-fin))

  fin'SumDep : (n : Nat) -> (f : (FinInd' n) -> D) -> D
  fin'SumDep zero    _ = 0#
  fin'SumDep (suc n) f = f zero + (fin'SumDep n (f ∘ suc))

  i<nSum : (n : Nat) -> (f : Nat -> D) -> D
  i<nSum n f = finSumDep n (\ (x , _) -> f x)

  enumerationSum : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationSum enum f = finSumDep _ (f ∘ enum)

  fin'SumDep-swap : {n : Nat} -> (sw : Swap n) -> (f : (FinInd' n) -> D)
                    -> fin'SumDep n f == fin'SumDep n (f ∘ finSwap sw)
  fin'SumDep-swap {n = (suc (suc n))} swap f = ans
    where
    ans1 : (f zero + f (suc zero)) == (f (suc zero) + (f zero))
    ans1 = +-commute

    f2 : FinInd' n -> D
    f2 x = f (suc (suc x))

    ans : (f zero + (f (suc zero) + fin'SumDep n f2))
          == (f (suc zero) + (f zero + fin'SumDep n f2))
    ans = sym +-assoc >=> +-left ans1 >=> +-assoc
  fin'SumDep-swap (swap-skip sw) f =
    cong (f zero +_) (fin'SumDep-swap sw (f ∘ suc))

  fin'SumDep-swapPerm' : {n : Nat} -> (l : Nat)
                         -> (sw : SwapPerm' n l) -> (f : (FinInd' n) -> D)
                         -> fin'SumDep n f == fin'SumDep n (f ∘ finSwapPerm' l sw)
  fin'SumDep-swapPerm' zero    sw f = refl
  fin'SumDep-swapPerm' (suc l) sw f = ans
    where
    rec : fin'SumDep _ (f ∘ finSwap (sw zero-fin)) ==
          fin'SumDep _ (f ∘ finSwap (sw zero-fin) ∘ finSwapPerm' l (sw ∘ suc-fin))
    rec = fin'SumDep-swapPerm' l (sw ∘ suc-fin) (f ∘ finSwap (sw zero-fin))

    ans : fin'SumDep _ f == fin'SumDep _ (f ∘ finSwap (sw zero-fin) ∘ finSwapPerm' l (sw ∘ suc-fin))
    ans = fin'SumDep-swap (sw zero-fin) f >=> rec

  fin'SumDep-swapPerm : {n : Nat}
                        -> (sw : SwapPerm n) -> (f : (FinInd' n) -> D)
                        -> fin'SumDep n f == fin'SumDep n (f ∘ finSwapPerm sw)
  fin'SumDep-swapPerm (l , sw) = fin'SumDep-swapPerm' l sw

i<nSum-zero : {n : Nat} -> i<nSum NatSemiring n (\i -> 0) == 0
i<nSum-zero {n = zero}  = refl
i<nSum-zero {n = suc n} = i<nSum-zero {n}

i<nSum-one : {n : Nat} -> i<nSum NatSemiring n (\i -> 1) == n
i<nSum-one {n = zero}  = refl
i<nSum-one {n = suc n} = cong suc (i<nSum-one {n})
