{-# OPTIONS --cubical --safe --exact-split #-}

module fin.sum-pair where

open import additive-group
open import additive-group.instances.nat
open import base
open import hlevel
open import nat

record FinPair+ (n : Nat) : Type₀ where
  constructor fin-pair+
  field
    i : Nat
    j : Nat
    i+j=n : i + j == n

FinPair+-path : {n : Nat} {p1 p2 : FinPair+ n} ->
                (FinPair+.i p1 == FinPair+.i p2) ->
                (FinPair+.j p1 == FinPair+.j p2) ->
                p1 == p2
FinPair+-path {n} {p1} {p2} q1 q2 i =
  fin-pair+ (q1 i) (q2 i)
    (isProp->PathPᵉ (\j -> isSetNat (q1 j + q2 j) n)
      (FinPair+.i+j=n p1)
      (FinPair+.i+j=n p2)
      i)
