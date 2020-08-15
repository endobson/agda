{-# OPTIONS --cubical --safe --exact-split #-}

module lcm where

open import base
open import div
open import gcd
open import nat

record LCM' (a : Nat) (b : Nat) (m : Nat) : Type₀ where
  field
    a%m : a div' m
    b%m : b div' m
    f : (x : Nat) -> (a div' x) -> (b div' x) -> (m div' x)

  m-pos : (Pos' a) -> (Pos' b) -> Pos' m
  m-pos a-pos b-pos = div'-pos->pos (f (a *' b) a%ab b%ab) (*'-Pos'-Pos' a-pos b-pos)
    where
    a%ab : a div' (a *' b)
    a%ab = b , *'-commute {b} {a}
    b%ab : b div' (a *' b)
    b%ab = a , refl

lcm-unique : {a b m1 m2 : Nat} -> LCM' a b m1 -> LCM' a b m2 -> m1 == m2
lcm-unique {a} {b} {m1} {m2} lcm1 lcm2 = div'-antisym m1%m2 m2%m1
  where
  module m1 = LCM' lcm1
  module m2 = LCM' lcm2

  m1%m2 : m1 div' m2
  m1%m2 = m1.f m2 m2.a%m m2.b%m
  m2%m1 : m2 div' m1
  m2%m1 = m2.f m1 m1.a%m m1.b%m

lcm-idempotent : {a b m : Nat} -> LCM' a b m -> LCM' a m m
lcm-idempotent l = record
  { a%m = LCM'.a%m l
  ; b%m = div'-refl
  ; f = \ x a%x m%x -> m%x
  }

lcm-absorbs-gcd : {a b d : Nat} -> GCD' a b d -> LCM' a d a
lcm-absorbs-gcd g = record
  { a%m = div'-refl
  ; b%m = GCD'.%a g
  ; f = \ x a%x d%x -> a%x
  }

gcd-absorbs-lcm : {a b m : Nat} -> LCM' a b m -> GCD' a m a
gcd-absorbs-lcm l = record
  { %a = div'-refl
  ; %b = LCM'.a%m l
  ; f = \x x%a x%m -> x%a
  }
