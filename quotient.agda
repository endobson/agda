{-# OPTIONS --cubical --safe --exact-split #-}

module quotient where

open import base
open import equality
open import nat

quotient : (a : Nat) (b : Nat⁺) -> Nat

private
  quotient-helper : (a : Nat) (x : Nat) (b : Nat⁺) -> Nat
  quotient-helper a       zero    b = quotient a b
  quotient-helper zero    (suc x) b = zero
  quotient-helper (suc a) (suc x) b = quotient-helper a x b

quotient zero    b              = zero
quotient (suc a) b@(suc b' , _) = suc (quotient-helper a b' b)

private
  quotient-helper-+' : {a : Nat} (x : Nat) {b : Nat⁺} -> quotient-helper (x +' a) x b == quotient a b
  quotient-helper-+' zero    = refl
  quotient-helper-+' (suc x) = quotient-helper-+' x

quotient-+' : {a : Nat} {b : Nat⁺} -> quotient (⟨ b ⟩ +' a) b == suc (quotient a b)
quotient-+' {b = ((suc b') , _)} = cong suc (quotient-helper-+' b')

quotient-*' : {a : Nat} {b : Nat⁺} -> quotient (a *' ⟨ b ⟩) b == a
quotient-*' {a = zero}    = refl
quotient-*' {a = (suc a)} = (quotient-+' >=> cong suc (quotient-*'))
