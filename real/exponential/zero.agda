{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.zero where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import fin
open import finite-commutative-monoid.instances
open import finset.instances
open import functions
open import funext
open import real.exponential-series
open import real.sequence.limit
open import ring.implementations.real
open import semiring
open import sequence.partial-sums

opaque
  exp0-path : exp 0# == 1#
  exp0-path =
    cong fst (isProp-isConvergentSequence
               (exp 0# , isLimit-exp 0#)
               (1# , lim2))
    where
    p1 : ∀ n -> exp-terms 0# (suc n) == 0#
    p1 n = *-right *-left-zero >=> *-right-zero

    p2 : ∀ n -> partial-sums (exp-terms 0# ∘ suc) n == 0#
    p2 n = finiteMerge-ε _ (\(i , _) -> p1 i)
    p3 : ∀ n -> partial-sums (exp-terms 0#) (suc n) == 1#
    p3 n = partial-sums-suc >=>
           +-right (p2 n) >=>
           +-right-zero >=>
           exp-term0

    lim1 : isLimit (partial-sums (exp-terms 0#) ∘ suc) 1#
    lim1 = subst2 isLimit (sym (funExt p3)) refl (isLimit-constant-seq 1#)
    lim2 : isLimit (partial-sums (exp-terms 0#)) 1#
    lim2 = dropN-reflects-limit lim1
