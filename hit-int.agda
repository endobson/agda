{-# OPTIONS --cubical --safe --exact-split #-}

module hit-int where

open import base
open import cubical
open import discrete
open import discrete.instances.top
open import equality-path
open import equivalence
open import hlevel
open import isomorphism
open import nat
open import sum
open import univalence

import int

data Int : Type₀ where
  nonneg : Nat -> Int
  nonpos : Nat -> Int
  same-zero : nonneg 0 == nonpos 0

ℤ : Type₀
ℤ = Int

int : Nat -> Int
int = nonneg

Int-eq : Int ≃ int.Int
Int-eq = isoToEquiv i
  where
  open Iso
  i : Iso Int int.Int
  i .fun (nonneg n)       = (int.nonneg n)
  i .fun (nonpos zero)    = (int.nonneg zero)
  i .fun (nonpos (suc n)) = (int.neg n)
  i .fun (same-zero i)    = (int.nonneg zero)
  i .inv (int.nonneg n)   = (nonneg n)
  i .inv (int.neg n)      = (nonpos (suc n))
  i .rightInv (int.nonneg n)  = refl
  i .rightInv (int.neg n)     = refl
  i .leftInv (nonneg n)       = refl
  i .leftInv (nonpos zero)    = same-zero
  i .leftInv (nonpos (suc n)) = refl
  i .leftInv (same-zero i)    = (\j -> same-zero (j ∧ i))

add1 : Int -> Int
add1 (nonneg x) = nonneg (suc x)
add1 (nonpos zero) = (add1 (nonneg zero))
add1 (nonpos (suc x)) = (nonpos x)
add1 (same-zero i) = nonneg (suc zero)

sub1 : Int -> Int
sub1 (nonneg (suc x)) = nonneg x
sub1 (nonneg zero) = (sub1 (nonpos zero))
sub1 (nonpos x) = (nonpos (suc x))
sub1 (same-zero i) = nonpos (suc zero)

add1-sub1 : ∀ z -> add1 (sub1 z) == z
add1-sub1 (nonneg (suc x)) = refl
add1-sub1 (nonneg zero) i = same-zero (~ i)
add1-sub1 (nonpos x) = refl
add1-sub1 (same-zero i) j = same-zero (i ∨ (~ j))

sub1-add1 : ∀ z -> sub1 (add1 z) == z
sub1-add1 (nonneg x) = refl
sub1-add1 (nonpos zero) i = same-zero i
sub1-add1 (nonpos (suc x)) = refl
sub1-add1 (same-zero i) j = same-zero (i ∧ j)

module _ where
  private
    Codes : Type₀
    Codes = (Top ⊎ (Nat ⊎ Nat))

    encode : Int -> Codes
    encode (nonneg zero) = inj-l tt
    encode (nonneg (suc n)) = inj-r (inj-l n)
    encode (nonpos zero) = inj-l tt
    encode (nonpos (suc n)) = inj-r (inj-r n)
    encode (same-zero i) = inj-l tt

    decode : Codes -> Int
    decode (inj-l _) = nonneg zero
    decode (inj-r (inj-l n)) = nonneg (suc n)
    decode (inj-r (inj-r n)) = nonpos (suc n)

    encode-decode : ∀ x -> encode (decode x) == x
    encode-decode (inj-l tt) = refl
    encode-decode (inj-r (inj-l n)) = refl
    encode-decode (inj-r (inj-r n)) = refl

    decode-encode : ∀ x -> decode (encode x) == x
    decode-encode (nonneg zero) = refl
    decode-encode (nonneg (suc n)) = refl
    decode-encode (nonpos zero) = same-zero
    decode-encode (nonpos (suc n)) = refl
    decode-encode (same-zero i) = \j -> same-zero (i ∧ j)

    encode-path : Int == Codes
    encode-path = isoToPath (iso encode decode encode-decode decode-encode)

  opaque
    Discrete-Int : Discrete Int
    Discrete-Int = subst Discrete (sym encode-path) (Discrete⊎ decide-= (Discrete⊎ decide-= decide-=))

    isSet-Int : isSet Int
    isSet-Int = Discrete->isSet Discrete-Int
