{-# OPTIONS --cubical --safe --exact-split #-}

module fraction.sign where

open import base
open import hlevel.base
open import rational
open import relation
open import semiring
open import ring.implementations
open import sign
open import sign.instances.int
open import sigma

import int.order

open import int using (Int ; ℤ)

private
  module i where
    open int.order public
    open int public

private
  numer : Rational' -> Int
  numer = Rational'.numerator
  denom : Rational' -> Int
  denom = Rational'.denominator
  rNonZero : (r : Rational') -> i.NonZero (denom r)
  rNonZero = Rational'.NonZero-denominator

isSignℚ' : Sign -> Pred Rational' ℓ-zero
isSignℚ' s q = isSign s (numer q * denom q)

Posℚ' : Rational' -> Type₀
Posℚ' = isSignℚ' pos-sign
Zeroℚ' : Rational' -> Type₀
Zeroℚ' = isSignℚ' zero-sign

NonNegℚ' : Rational' -> Type₀
NonNegℚ' q = i.NonNeg (numer q i.* denom q)

ℚ'->sign : Rational' -> Sign
ℚ'->sign q = i.int->sign (numer q i.* denom q)

isProp-isSignℚ' : (s : Sign) (q : Rational') -> isProp (isSignℚ' s q)
isProp-isSignℚ' s q = isProp-isSign s (numer q * denom q)

isSignℚ'-unique : (q : Rational') (s1 s2 : Sign) ->
                  (isSignℚ' s1 q) -> (isSignℚ' s2 q) -> s1 == s2
isSignℚ'-unique q s1 s2 = isSign-unique (numer q * denom q) s1 s2
