{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.instances.nat where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import nat
open import semiring

instance
  NatSemiring : Semiring AdditiveCommMonoid-Nat
  NatSemiring = record
    { 1# = 1
    ; _*_ = _*'_
    ; *-assoc = (\ {m} {n} {o} -> (*'-assoc {m} {n} {o}))
    ; *-commute = (\ {m} {n} -> (*'-commute {m} {n}))
    ; *-left-zero = refl
    ; *-left-one = +'-right-zero
    ; *-distrib-+-right = (\ {m} {n} {o} -> *'-distrib-+' {m} {n} {o})
    ; isSet-Domain = isSetNat
    }
