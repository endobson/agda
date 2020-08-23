{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.propisitional where

open import base
open import div
open import int
open import nat


record GCD (a : Int) (b : Int) (d : Int) : Type₀ where
  constructor gcd
  field
    non-neg : (NonNeg d)
    %a : d div a
    %b : d div b
    f : (x : Int) -> x div a -> x div b -> x div d

record GCD' (a : Nat) (b : Nat) (d : Nat) : Type₀ where
  field
    %a : d div' a
    %b : d div' b
    f : (x : Nat) -> x div' a -> x div' b -> x div' d

GCD⁺ : Nat⁺ -> Nat⁺ -> Nat⁺ -> Type₀
GCD⁺ (a , _) (b , _) (d , _) = GCD' a b d
