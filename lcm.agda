{-# OPTIONS --cubical --safe --exact-split #-}

module lcm where

open import base
open import div
open import nat

record LCM' (a : Nat) (b : Nat) (m : Nat) : Type₀ where
  field
    a%m : a div' m
    b%m : b div' m
    f : (x : Nat) -> (a div' x) -> (b div' x) -> (m div' x)

lcm-unique : {a b m1 m2 : Nat} -> LCM' a b m1 -> LCM' a b m2 -> m1 == m2
lcm-unique {a} {b} {m1} {m2} lcm1 lcm2 = div'-antisym m1%m2 m2%m1
  where
  module m1 = LCM' lcm1
  module m2 = LCM' lcm2

  m1%m2 : m1 div' m2
  m1%m2 = m1.f m2 m2.a%m m2.b%m
  m2%m1 : m2 div' m1
  m2%m1 = m2.f m1 m1.a%m m1.b%m
