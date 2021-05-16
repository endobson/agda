{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order where

open import base
open import equality
open import hlevel
open import rational
open import relation

import int.order
import int

open int using (Int)

private
  module i where
    open int.order public
    open int public

private
  numer : Rational' -> Int
  numer = Rational'.numerator
  denom : Rational' -> Int
  denom = Rational'.denominator

_<'_ : Rational' -> Rational' -> Type₀
q <' r = ((numer q) i.* (denom r)) i.< ((numer r) i.* (denom q))

_>'_ : Rational' -> Rational' -> Type₀
q >' r = q <' r

isProp-<' : {q r : Rational'} -> isProp (q <' r)
isProp-<' = i.isProp-<

--refl-<' : Reflexive _<'_
--refl-<' = i.refl-≤

module _ {q r s : Rational'}
         (pos-q : i.Pos (denom q))
         (pos-s : i.Pos (denom s))
         (pos-r : i.Pos (denom r)) where

  trans-<' : q <' r -> r <' s -> q <' s
  trans-<' q<r r<s = check6
    where

    check1 : ((numer q) i.* (denom r)) i.< ((numer r) i.* (denom q))
    check1 = q<r
    check2 : ((numer r) i.* (denom s)) i.< ((numer s) i.* (denom r))
    check2 = r<s

    check3 : (((numer r) i.* (denom s)) i.* (denom q)) i.< (((numer s) i.* (denom r)) i.* (denom q))
    check3 = i.*₂-Pos-preserves-<⁺ r<s pos-q

    check4 : (((numer q) i.* (denom r)) i.* (denom s)) i.< (((numer r) i.* (denom s)) i.* (denom q))
    check4 = subst2 i._<_ refl (i.*-assoc >=> i.*-right i.*-commute >=> sym i.*-assoc)
                    (i.*₂-Pos-preserves-<⁺ q<r pos-s)

    check5 : ((denom r) i.* ((numer q) i.* (denom s))) i.< ((denom r) i.* ((numer s) i.* (denom q)))
    check5 = subst2 i._<_ (i.*-left i.*-commute >=> i.*-assoc) (i.*-left i.*-commute >=> i.*-assoc)
                    (i.trans-< check4 check3)

    check6 : ((numer q) i.* (denom s)) i.< ((numer s) i.* (denom q))
    check6 = i.*₁-Pos-preserves-<⁻ check5 pos-r
