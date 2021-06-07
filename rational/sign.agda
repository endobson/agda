{-# OPTIONS --cubical --safe --exact-split #-}

module rational.sign where

open import base
open import equality
open import hlevel
open import isomorphism
open import rational
open import relation
open import semiring
open import ring.implementations
open import sign
open import sign.instances.int
open import sign.instances.fraction
open import sigma
open import univalence

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


r~-preserves-sign : {q1 q2 : Rational'} {s : Sign} -> isSign s q1 -> q1 r~ q2 -> isSign s q2
r~-preserves-sign {q1} {q2} {s} v p = ans
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
  expand-s = i.isSign-unique v (i.isSign-self (n1 i.* d1))

  end-path : s == S (n2 i.* d2)
  end-path = expand-s >=> i.int->sign-preserves-* >=> path >=> (sym i.int->sign-preserves-*)

  ans : i.isSign s (n2 i.* d2)
  ans = subst (\s -> i.isSign s (n2 i.* d2)) (sym end-path) (i.isSign-self (n2 i.* d2))

private

  isSign-full : Sign -> Rational -> hProp ℓ-zero
  isSign-full s = RationalElim.elim (\_ -> isSet-hProp) val preserved
    where
    val : Rational' -> hProp ℓ-zero
    val r = isSign s r , isProp-isSign s r
    preserved : (a b : Rational') -> (a r~ b) -> val a == val b
    preserved a b a~b = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (isSign s a) (isSign s b)
      i .fun p = r~-preserves-sign {a} {b} {s} p a~b
      i .inv p = r~-preserves-sign {b} {a} {s} p (sym a~b)
      i .rightInv p = i.isProp-isSign s _ p
      i .leftInv p = i.isProp-isSign s _ p

isSignℚ : Sign -> Pred Rational ℓ-zero
isSignℚ s r = fst (isSign-full s r)

isProp-isSignℚ : (s : Sign) -> (r : Rational) -> isProp (isSignℚ s r)
isProp-isSignℚ s r = snd (isSign-full s r)

isSignℚ-unique : (r : Rational) (s1 s2 : Sign)-> isSignℚ s1 r -> isSignℚ s2 r -> s1 == s2
isSignℚ-unique r s1 s2 =
  RationalElim.elimProp
    {C = \r -> isSignℚ s1 r -> isSignℚ s2 r -> s1 == s2}
    (\_ -> isPropΠ2 (\ _ _ -> isSet-Sign s1 s2))
    (\r v1 v2 -> isSign-unique r s1 s2 v1 v2)
    r
