{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order where

open import base
open import equality
open import hlevel
open import isomorphism
open import rational
open import relation
open import sigma
open import sign
open import univalence

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
  rNonZero : (r : Rational') -> i.NonZero (denom r)
  rNonZero = Rational'.NonZero-denominator

private
  isSign' : Sign -> Pred Rational' ℓ-zero
  isSign' s q = i.isSign s (numer q i.* denom q)

  Pos' : Rational' -> Type₀
  Pos' = isSign' pos-sign
  Zero' : Rational' -> Type₀
  Zero' = isSign' zero-sign


_<'_ : Rational' -> Rational' -> Type₀
q <' r = Pos' (r r+' (r-' q))

_>'_ : Rational' -> Rational' -> Type₀
q >' r = q <' r

isProp-<' : {q r : Rational'} -> isProp (q <' r)
isProp-<' = i.isPropPos

r~-preserves-sign : {q1 q2 : Rational'} {s : Sign} -> isSign' s q1 -> q1 r~ q2 -> isSign' s q2
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

r~-preserves-<₁ : {q1 q2 r : Rational'} -> q1 <' r -> q1 r~ q2 -> q2 <' r
r~-preserves-<₁ {q1} {q2} {r} q1<r q1~q2 =
  r~-preserves-sign {r r+' (r-' q1)} {r r+' (r-' q2)} {s = pos-sign} q1<r
    (r+'-preserves-r~₂ r (r-' q1) (r-' q2) (r-'-preserves-r~ q1 q2 q1~q2))

r~-preserves-<₂ : {q r1 r2 : Rational'} -> q <' r1 -> r1 r~ r2 -> q <' r2
r~-preserves-<₂ {q} {r1} {r2} q<r1 r1~r2 =
  r~-preserves-sign {r1 r+' (r-' q)} {r2 r+' (r-' q)} {s = pos-sign} q<r1
    (r+'-preserves-r~₁ (r-' q) r1 r2 r1~r2)

r+'-preserves-Pos' : {q1 q2 : Rational'} -> Pos' q1 -> Pos' q2 -> Pos' (q1 r+' q2)
r+'-preserves-Pos' {q1} {q2} p1 p2 = ans2
  where
  n1 = numer q1
  n2 = numer q2
  d1 = denom q1
  d2 = denom q2

  helper2 : (q : Rational') -> Pos' q -> Σ[ s ∈ Sign ] (i.isSign s (numer q) × i.isSign s (denom q))
  helper2 q p = s1 , (i.isSign-self (numer q) ,
                      subst (\x -> i.isSign x (denom q)) (sym path) (i.isSign-self (denom q)))
    where
    s1 = i.int->sign (numer q)
    s2 = i.int->sign (denom q)
    path : s1 == s2
    path = handle s1 s2 (subst isPosSign i.int->sign-preserves-* (i.Pos->PosSign p))
      where
      handle : (x y : Sign) -> isPosSign (x s* y) -> x == y
      handle pos-sign pos-sign _ = refl
      handle neg-sign neg-sign _ = refl
      handle pos-sign  zero-sign ()
      handle zero-sign zero-sign ()
      handle neg-sign  zero-sign ()

  helper : (s1 s2 : Sign) -> i.isSign s1 n1 -> i.isSign s1 d1 -> i.isSign s2 n2 -> i.isSign s2 d2 ->
           i.Pos ((n1 i.* d2 i.+ n2 i.* d1) i.* (d1 i.* d2))
  helper zero-sign s2        sn1 sd1 sn2 sd2 = bot-elim (i.NonZero->¬Zero (rNonZero q1) sd1)
  helper pos-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (i.NonZero->¬Zero (rNonZero q2) sd2)
  helper neg-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (i.NonZero->¬Zero (rNonZero q2) sd2)
  helper pos-sign  pos-sign  sn1 sd1 sn2 sd2 =
    i.*-Pos-Pos (i.+-Pos-Pos (i.*-Pos-Pos sn1 sd2) (i.*-Pos-Pos sn2 sd1)) (i.*-Pos-Pos sd1 sd2)
  helper pos-sign  neg-sign  sn1 sd1 sn2 sd2 =
    i.*-Neg-Neg (i.+-Neg-Neg (i.*-Pos-Neg sn1 sd2) (i.*-Neg-Pos sn2 sd1)) (i.*-Pos-Neg sd1 sd2)
  helper neg-sign  pos-sign  sn1 sd1 sn2 sd2 =
    i.*-Neg-Neg (i.+-Neg-Neg (i.*-Neg-Pos sn1 sd2) (i.*-Pos-Neg sn2 sd1)) (i.*-Neg-Pos sd1 sd2)
  helper neg-sign  neg-sign  sn1 sd1 sn2 sd2 =
    i.*-Pos-Pos (i.+-Pos-Pos (i.*-Neg-Neg sn1 sd2) (i.*-Neg-Neg sn2 sd1)) (i.*-Neg-Neg sd1 sd2)

  ans : i.Pos ((n1 i.* d2 i.+ n2 i.* d1) i.* (d1 i.* d2))
  ans = helper s1 s2 sn1 sd1 sn2 sd2
    where
    full-s1 = helper2 q1 p1
    full-s2 = helper2 q2 p2
    s1 = fst full-s1
    sn1 = proj₁ (snd full-s1)
    sd1 = proj₂ (snd full-s1)
    s2 = fst full-s2
    sn2 = proj₁ (snd full-s2)
    sd2 = proj₂ (snd full-s2)

  ans2 : Pos' (q1 r+' q2)
  ans2 = subst Pos' (sym r+'-eval) ans

Zero'-0r' : Zero' 0r'
Zero'-0r' = subst i.Zero (sym i.*-left-zero) tt

irrefl-<' : Irreflexive _<'_
irrefl-<' {a} a<a = (i.NonPos->¬Pos (i.Zero->NonPos b-zero) b-pos)
  where
  b = a r+' (r-' a)

  b-pos : Pos' b
  b-pos = a<a
  b-zero : Zero' b
  b-zero = r~-preserves-sign {0r'} {b} {zero-sign} Zero'-0r' (sym (r+'-inverse a))

trans-<' : Transitive _<'_
trans-<' {a} {b} {c} a<b b<c = a<c
  where
  d = b r+' (r-' a)
  e = c r+' (r-' b)
  f = c r+' (r-' a)

  step1 : (e r+' d) r~' (c r+' ((r-' b) r+' d))
  step1 = r~->r~' r+'-assoc

  step2 : (c r+' ((r-' b) r+' d)) r~' (c r+' (((r-' b) r+' b) r+' (r-' a)))
  step2 = r~->r~' (r+'-preserves-r~₂ c _ _ (sym r+'-assoc))

  step3 : ((r-' b) r+' b) r~ 0r'
  step3 = (subst (_r~ 0r') (r+'-commute b (r-' b)) (r+'-inverse b))

  step4 : (c r+' (((r-' b) r+' b) r+' (r-' a))) r~' (c r+' (0r' r+' (r-' a)))
  step4 = r~->r~' (r+'-preserves-r~₂ _ _ _ (r+'-preserves-r~₁ _ _ _ step3))

  step5 : (c r+' (0r' r+' (r-' a))) r~' (c r+' (r-' a))
  step5 = r~->r~' (path->r~ (cong (c r+'_) (r+'-left-zero (r-' a))))

  combined-steps : (e r+' d) r~' f
  combined-steps = trans-r~' (trans-r~' (trans-r~' step1 step2) step4) step5

  f-path : (e r+' d) r~ f
  f-path = r~'->r~ combined-steps

  a<c : a <' c
  a<c = r~-preserves-sign {e r+' d} {f} {s = pos-sign} (r+'-preserves-Pos' b<c a<b) f-path


private
  isSign-full : Sign -> Rational -> hProp ℓ-zero
  isSign-full s = RationalElim.elim (\_ -> isSet-hProp) val preserved
    where
    val : Rational' -> hProp ℓ-zero
    val r = isSign' s r , i.isProp-isSign s
    preserved : (a b : Rational') -> (a r~ b) -> val a == val b
    preserved a b a~b = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      open Iso
      i : Iso (isSign' s a) (isSign' s b)
      i .fun p = r~-preserves-sign {a} {b} {s} p a~b
      i .inv p = r~-preserves-sign {b} {a} {s} p (sym a~b)
      i .rightInv p = i.isProp-isSign s _ p
      i .leftInv p = i.isProp-isSign s _ p

isSign : Sign -> Pred Rational ℓ-zero
isSign s r = fst (isSign-full s r)

isProp-isSign : (s : Sign) -> {r : Rational} -> isProp (isSign s r)
isProp-isSign s {r} = snd (isSign-full s r)

isSign-unique : {r : Rational} {s1 s2 : Sign} -> isSign s1 r -> isSign s2 r -> s1 == s2
isSign-unique {r} {s1} {s2} =
  RationalElim.elimProp
    {C = \r -> isSign s1 r -> isSign s2 r -> s1 == s2}
    (\_ -> isPropΠ2 (\ _ _ -> isSet-Sign s1 s2))
    (\r v1 v2 -> i.isSign-unique {_} {s1} {s2} v1 v2)
    r


private
  Pos : Rational -> Type₀
  Pos = isSign pos-sign

_<_ : Rational -> Rational -> Type₀
q < r = Pos (r r+ (r- q))

_>_ : Rational -> Rational -> Type₀
q > r = q < r

isProp-< : {a b : Rational} -> isProp (a < b)
isProp-< {a} {b} = isProp-isSign pos-sign {b r+ (r- a)}

irrefl-< : Irreflexive _<_
irrefl-< {a} a<a =
  RationalElim.elimProp
    {C = (\r -> r < r -> Bot)}
    (\_ -> isPropΠ (\_ -> isPropBot))
    (\r -> irrefl-<' {r}) a a<a

trans-< : Transitive _<_
trans-< {a} {b} {c} a<b b<c =
  RationalElim.elimProp3
    {C3 = (\a b c -> a < b -> b < c -> a < c)}
    (\a _ c -> isPropΠ2 (\_ _ -> isProp-< {a} {c}))
    (\a b c a<b b<c -> trans-<' a<b b<c) a b c a<b b<c

asym-< : Asymmetric _<_
asym-< {a} {b} lt1 lt2 = irrefl-< {a} (trans-< {a} {b} {a} lt1 lt2)
