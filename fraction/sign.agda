{-# OPTIONS --cubical --safe --exact-split #-}

module fraction.sign where

open import base
open import equality
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

record isSignℚ' (s : Sign) (q : Rational') : Type₀ where
  field
    v : isSign s (numer q * denom q)

is-signℚ' : {s : Sign} {q : Rational'} -> isSign s (numer q * denom q) -> isSignℚ' s q
is-signℚ' v = record { v = v }

-- isSignℚ' : Sign -> Pred Rational' ℓ-zero
-- isSignℚ' s q = isSign s (numer q * denom q)

Posℚ' : Rational' -> Type₀
Posℚ' = isSignℚ' pos-sign
Zeroℚ' : Rational' -> Type₀
Zeroℚ' = isSignℚ' zero-sign

ℚ'->sign : Rational' -> Sign
ℚ'->sign q = i.int->sign (numer q i.* denom q)

isProp-isSignℚ' : (s : Sign) (q : Rational') -> isProp (isSignℚ' s q)
isProp-isSignℚ' s q a b =
  cong is-signℚ' (isProp-isSign s (numer q * denom q) (isSignℚ'.v a) (isSignℚ'.v b) )

isSignℚ'-unique : (q : Rational') (s1 s2 : Sign) ->
                  (isSignℚ' s1 q) -> (isSignℚ' s2 q) -> s1 == s2
isSignℚ'-unique q s1 s2 p1 p2 = isSign-unique (numer q * denom q) s1 s2 (isSignℚ'.v p1) (isSignℚ'.v p2)

NonNeg-nd->ℚ' : {q : Rational'} -> NonNeg (numer q * denom q) -> Posℚ' q ⊎ Zeroℚ' q
NonNeg-nd->ℚ' (inj-l p) = inj-l (is-signℚ' p)
NonNeg-nd->ℚ' (inj-r p) = inj-r (is-signℚ' p)
