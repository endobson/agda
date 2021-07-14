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

Posℚ' : Rational' -> Type₀
Posℚ' = isSignℚ' pos-sign
Zeroℚ' : Rational' -> Type₀
Zeroℚ' = isSignℚ' zero-sign


isProp-isSignℚ' : (s : Sign) (q : Rational') -> isProp (isSignℚ' s q)
isProp-isSignℚ' s q a b =
  cong is-signℚ' (isProp-isSign s (numer q * denom q) (isSignℚ'.v a) (isSignℚ'.v b) )

isSignℚ'-unique : (q : Rational') (s1 s2 : Sign) ->
                  (isSignℚ' s1 q) -> (isSignℚ' s2 q) -> s1 == s2
isSignℚ'-unique q s1 s2 p1 p2 = isSign-unique (numer q * denom q) s1 s2 (isSignℚ'.v p1) (isSignℚ'.v p2)

instance
  SignStr-ℚ' : SignStr ℚ' ℓ-zero
  SignStr-ℚ' = record
    { isSign = isSignℚ'
    ; isProp-isSign = isProp-isSignℚ'
    ; isSign-unique = isSignℚ'-unique
    }

ℚ'->sign : Rational' -> Sign
ℚ'->sign q = i.int->sign (numer q i.* denom q)

isSign'-self : (q : Rational') -> isSign (ℚ'->sign q) q
isSign'-self q = is-signℚ' (i.isSign-self (numer q i.* denom q))

NonNeg-nd->ℚ' : {q : ℚ'} -> NonNeg (numer q * denom q) -> NonNeg q
NonNeg-nd->ℚ' (inj-l p) = inj-l (is-signℚ' p)
NonNeg-nd->ℚ' (inj-r p) = inj-r (is-signℚ' p)

r~-preserves-sign : {q1 q2 : ℚ'} {s : Sign} -> isSign s q1 -> q1 r~ q2 -> isSign s q2
r~-preserves-sign {q1} {q2} {s} v p = is-signℚ' ans
  where
  n1 = numer q1
  n2 = numer q2
  d1 = denom q1
  d2 = denom q2
  S = i.int->sign

  inner-path : S n1 s* S d2 == S n2 s* S d1
  inner-path = sym i.int->sign-preserves-* >=> cong S p >=> i.int->sign-preserves-*

  path : (S n1) s* (S d1) == (S n2) s* (S d2)
  path =
    begin
      (S n1) s* (S d1)
    ==< sym (s*₁-NonZero-order2 (i.NonZero->NonZeroSign (Rational'.NonZero-denominator q2))) >
      (S d2) s* ((S d2) s* ((S n1) s* (S d1)))
    ==< cong (S d2 s*_) (sym s*-assoc >=> (cong (_s* (S d1)) (s*-commute >=> inner-path))) >
      (S d2) s* (((S n2) s* (S d1)) s* (S d1))
    ==< cong (S d2 s*_) (s*₂-NonZero-order2 (i.NonZero->NonZeroSign (Rational'.NonZero-denominator q1))) >
      (S d2) s* (S n2)
    ==< s*-commute >
      (S n2) s* (S d2)
    end

  expand-s : s == S (n1 i.* d1)
  expand-s = i.isSign-unique (isSignℚ'.v v) (i.isSign-self (n1 i.* d1))

  end-path : s == S (n2 i.* d2)
  end-path = expand-s >=> i.int->sign-preserves-* >=> path >=> (sym i.int->sign-preserves-*)

  ans : i.isSign s (n2 i.* d2)
  ans = subst (\s -> i.isSign s (n2 i.* d2)) (sym end-path) (i.isSign-self (n2 i.* d2))

-- r~-preserves-NonNeg : {q1 q2 : ℚ'} -> NonNeg q1 -> q1 r~ q2 -> NonNeg q2
-- r~-preserves-NonNeg {q1} {q2} nn-q1 r = handle (ℚ'->sign q1) (isSign'-self q1)
--   where
--   handle : (s : Sign) -> isSign s q1 -> NonNeg q2
--   handle pos-sign p-q1 = Pos->NonNeg (r~-preserves-sign p-q1 r)
--   handle zero-sign z-q1 = Zero->NonNeg (r~-preserves-sign z-q1 r)
--   handle neg-sign n-q1  = bot-elim (NonNeg->¬Neg nn-q1 n-q1)
