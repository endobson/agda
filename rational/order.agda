{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order where

open import base
open import equality
open import hlevel
open import isomorphism
open import rational
open import relation
open import set-quotient
open import sigma
open import sign
open import univalence
open import ring
open import ring.implementations.rational

import int.order
import int
import nat

open int using (Int)
open nat using (ℕ ; Nat⁺)

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

ℚ'->sign : Rational' -> Sign
ℚ'->sign q = i.int->sign (numer q i.* denom q)

isSign'-unique : (q : Rational') (s1 s2 : Sign) -> isSign' s1 q -> isSign' s2 q -> s1 == s2
isSign'-unique q s1 s2 = i.isSign-unique

isSign'-self : (q : Rational') -> isSign' (ℚ'->sign q) q
isSign'-self q = i.isSign-self (numer q i.* denom q)

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

private
  Pos->same-sign :
    (q : Rational') -> Pos' q -> Σ[ s ∈ Sign ] (i.isSign s (numer q) × i.isSign s (denom q))
  Pos->same-sign q p = s1 , (i.isSign-self (numer q) ,
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


r+'-preserves-Pos' : {q1 q2 : Rational'} -> Pos' q1 -> Pos' q2 -> Pos' (q1 r+' q2)
r+'-preserves-Pos' {q1} {q2} p1 p2 = ans2
  where
  n1 = numer q1
  n2 = numer q2
  d1 = denom q1
  d2 = denom q2

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
    full-s1 = Pos->same-sign q1 p1
    full-s2 = Pos->same-sign q2 p2
    s1 = fst full-s1
    sn1 = proj₁ (snd full-s1)
    sd1 = proj₂ (snd full-s1)
    s2 = fst full-s2
    sn2 = proj₁ (snd full-s2)
    sd2 = proj₂ (snd full-s2)

  ans2 : Pos' (q1 r+' q2)
  ans2 = subst Pos' (sym r+'-eval) ans


r*'-preserves-Pos' : {q1 q2 : Rational'} -> Pos' q1 -> Pos' q2 -> Pos' (q1 r*' q2)
r*'-preserves-Pos' {q1} {q2} p1 p2 = ans
  where
  n1 = numer q1
  n2 = numer q2
  d1 = denom q1
  d2 = denom q2

  helper : (s1 s2 : Sign) -> i.isSign s1 n1 -> i.isSign s1 d1 -> i.isSign s2 n2 -> i.isSign s2 d2 ->
           i.Pos ((n1 i.* n2) i.* (d1 i.* d2))
  helper zero-sign s2        sn1 sd1 sn2 sd2 = bot-elim (i.NonZero->¬Zero (rNonZero q1) sd1)
  helper pos-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (i.NonZero->¬Zero (rNonZero q2) sd2)
  helper neg-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (i.NonZero->¬Zero (rNonZero q2) sd2)
  helper pos-sign  pos-sign  sn1 sd1 sn2 sd2 =
    i.*-Pos-Pos (i.*-Pos-Pos sn1 sn2) (i.*-Pos-Pos sd1 sd2)
  helper pos-sign  neg-sign  sn1 sd1 sn2 sd2 =
    i.*-Neg-Neg (i.*-Pos-Neg sn1 sn2) (i.*-Pos-Neg sd1 sd2)
  helper neg-sign  pos-sign  sn1 sd1 sn2 sd2 =
    i.*-Neg-Neg (i.*-Neg-Pos sn1 sn2) (i.*-Neg-Pos sd1 sd2)
  helper neg-sign  neg-sign  sn1 sd1 sn2 sd2 =
    i.*-Pos-Pos (i.*-Neg-Neg sn1 sn2) (i.*-Neg-Neg sd1 sd2)

  ans : i.Pos ((n1 i.* n2) i.* (d1 i.* d2))
  ans = helper s1 s2 sn1 sd1 sn2 sd2
    where
    full-s1 = Pos->same-sign q1 p1
    full-s2 = Pos->same-sign q2 p2
    s1 = fst full-s1
    sn1 = proj₁ (snd full-s1)
    sd1 = proj₂ (snd full-s1)
    s2 = fst full-s2
    sn2 = proj₁ (snd full-s2)
    sd2 = proj₂ (snd full-s2)

r1/'-preserves-Pos' : (q : Rational') -> (i : ℚInv' q) -> Pos' q -> Pos' (r1/' q i)
r1/'-preserves-Pos' q i p = subst i.Pos i.*-commute p

r-'-flips-sign : (q : Rational') (s : Sign) -> (isSign' s q) -> (isSign' (s⁻¹ s) (r-' q))
r-'-flips-sign q s qs =
  subst (i.isSign (s⁻¹ s)) (sym i.minus-extract-left) (i.minus-isSign {numer q i.* denom q} {s} qs)

Zero'-0r' : Zero' 0r'
Zero'-0r' = subst i.Zero (sym i.*-left-zero) tt

Zero'-r~ : (q : Rational') -> Zero' q -> q r~ 0r'
Zero'-r~ q zq = cong (i._* (denom 0r')) path >=> i.*-left-zero >=> sym i.*-left-zero
  where
  path : (numer q) == (i.int 0)
  path = i.*-left-zero-eq (rNonZero q) (i.Zero-path ((numer q) i.* (denom q))  zq)

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


decide-<' : Decidable2 _<'_
decide-<' x y = handle (i.int->sign z') (i.isSign-self z')
  where
  z = y r+' (r-' x)
  z' = numer z i.* denom z
  handle : (s : Sign) -> (i.isSign s z') -> Dec (x <' y)
  handle pos-sign pz = yes pz
  handle zero-sign zz = no (\ pz -> i.NonPos->¬Pos (i.Zero->NonPos zz) pz)
  handle neg-sign nz = no (\ pz -> i.NonPos->¬Pos (i.Neg->NonPos nz) pz)




private
  Dense : {ℓ ℓA : Level} {A : Type ℓA} -> Rel A ℓ -> Type (ℓ-max ℓA ℓ)
  Dense {A = A} _<_ = {x y : A} -> x < y -> Σ[ z ∈ A ] (x < z × z < y)


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

ℚ->sign : Rational -> Sign
ℚ->sign = RationalElim.rec isSet-Sign ℚ'->sign preserved
  where
  preserved : (q1 q2 : Rational') -> (q1 r~ q2) -> (ℚ'->sign q1) == (ℚ'->sign q2)
  preserved q1 q2 r =
    isSign'-unique q2 _ _
      (r~-preserves-sign {q1} {q2} {ℚ'->sign q1} (isSign'-self q1) r)
      (isSign'-self q2)

isSign-self : (q : Rational) -> isSign (ℚ->sign q) q
isSign-self =
  RationalElim.elimProp
    (\q -> isProp-isSign (ℚ->sign q) {q})
    isSign'-self

private
  Pos : Rational -> Type₀
  Pos = isSign pos-sign
  Zero : Rational -> Type₀
  Zero = isSign zero-sign

Zero-path : (q : Rational) -> Zero q -> q == 0r
Zero-path =
  RationalElim.elimProp
    (\_ -> isPropΠ (\_ -> isSetRational _ _))
    (\q zq -> eq/ _ _ (Zero'-r~ q zq))



r*-preserves-Pos : (q1 q2 : Rational) -> Pos q1 -> Pos q2 -> Pos (q1 r* q2)
r*-preserves-Pos =
  RationalElim.elimProp2
    {C2 = \q1 q2 -> Pos q1 -> Pos q2 -> Pos (q1 r* q2)}
    (\q1 q2 -> isPropΠ2 (\ _ _ -> isProp-isSign pos-sign {q1 r* q2}))
    (\q1 q2 p1 p2 -> r*'-preserves-Pos' {q1} {q2} p1 p2)

r--flips-sign : (q : Rational) (s : Sign) -> (isSign s q) -> (isSign (s⁻¹ s) (r- q))
r--flips-sign =
  RationalElim.elimProp
    (\q -> isPropΠ2 (\ s _ -> isProp-isSign (s⁻¹ s) {r- q}))
    r-'-flips-sign


_<_ : Rational -> Rational -> Type₀
q < r = Pos (r r+ (r- q))

_>_ : Rational -> Rational -> Type₀
q > r = r < q

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

Pos-1/ℕ : (n : Nat⁺) -> Pos (1/ℕ n)
Pos-1/ℕ (n@(suc _) , _) = i.*-Pos-Pos tt tt

Pos-0< : (q : Rational) -> Pos q -> 0r < q
Pos-0< q = subst Pos p
  where
  p : q == q r+ (r- 0r)
  p = sym (r+-right-zero q)

Pos-1r : Pos 1r
Pos-1r = Pos-1/ℕ nat.1⁺

dense-< : Dense _<_
dense-< {x} {y} lt = z , (pos-d3 , pos-d4)
  where
  d1 = y r+ (r- x)
  d2 = d1 r* 1/2r
  z = x r+ d2
  z' = y r+ (r- d2)
  d3 = z r+ (r- x)
  d4 = y r+ (r- z)

  d2-path : d2 r+ d2 == d1
  d2-path = 1/2r-path d1

  z-path : z == z'
  z-path =
    begin
      x r+ d2
    ==< sym (r+-right-zero _) >
      (x r+ d2) r+ 0r
    ==< cong ((x r+ d2) r+_) (sym (r+-inverse d2)) >
      (x r+ d2) r+ (d2 r+ (r- d2))
    ==< r+-assoc x d2 (d2 r+ (r- d2)) >=>
        cong (x r+_) (sym (r+-assoc d2 d2 (r- d2)) >=> (cong (_r+ (r- d2)) d2-path)) >
      x r+ (d1 r+ (r- d2))
    ==< sym (r+-assoc x d1 (r- d2)) >
      (x r+ (y r+ (r- x))) r+ (r- d2)
    ==< cong (_r+ (r- d2)) (sym (r+-assoc x y (r- x)) >=>
                            cong (_r+ (r- x)) (r+-commute x y) >=>
                            r+-assoc y x (r- x) >=>
                            cong (y r+_) (r+-inverse x) >=>
                            r+-right-zero y) >
      y r+ (r- d2)
    end

  pos-d1 : Pos d1
  pos-d1 = lt

  pos-d2 : Pos d2
  pos-d2 = r*-preserves-Pos d1 1/2r pos-d1 (Pos-1/ℕ (2 , tt))

  d3-path : d2 == d3
  d3-path =
    sym (cong (_r+ (r- x)) (r+-commute x d2) >=>
         r+-assoc d2 x (r- x) >=>
         cong (d2 r+_) (r+-inverse x) >=>
         r+-right-zero d2)
  pos-d3 : Pos d3
  pos-d3 = subst Pos d3-path pos-d2

  d4-path : d2 == d4
  d4-path =
    sym (cong (\z -> y r+ (r- z)) z-path >=>
         cong (y r+_) (RationalRing.minus-distrib-plus {y} {r- d2}) >=>
         sym (r+-assoc y (r- y) (r- (r- d2))) >=>
         cong2 _r+_ (r+-inverse y) (RationalRing.minus-double-inverse {d2}) >=>
         r+-left-zero d2)
  pos-d4 : Pos d4
  pos-d4 = subst Pos d4-path pos-d2


decide-< : Decidable2 _<_
decide-< = RationalElim.elimProp2 (\a b -> isPropDec (isProp-< {a} {b})) decide-<'

private
  zero-diff->path : (x y : Rational) -> Zero (y r+ (r- x)) -> x == y
  zero-diff->path x y zyx = sym p
    where
    p : y == x
    p = sym (r+-right-zero y) >=>
        (cong (y r+_) (sym (r+-inverse x) >=> r+-commute x (r- x))) >=>
        sym (r+-assoc y (r- x) x) >=>
        cong (_r+ x) (Zero-path (y r+ (r- x)) zyx) >=>
        r+-left-zero x

connected-< : Connected _<_
connected-< {x} {y} x≮y y≮x =
  handle (ℚ->sign z) (isSign-self z)
  where
  z = (y r+ (r- x))
  z2 = (x r+ (r- y))
  p : (r- z) == z2
  p =
    (RationalRing.minus-distrib-plus {y} {r- x}) >=>
    cong ((r- y) r+_) (RationalRing.minus-double-inverse {x}) >=>
    r+-commute (r- y) x

  handle : (s : Sign) -> isSign s z -> x == y
  handle pos-sign pz = bot-elim (x≮y pz)
  handle zero-sign zz = zero-diff->path x y zz
  handle neg-sign nz = bot-elim (y≮x (subst Pos p (r--flips-sign z neg-sign nz)))

trichotomous-< : Trichotomous _<_
trichotomous-< x y = handle (decide-< x y) (decide-< y x)
  where
  handle : Dec (x < y) -> Dec (y < x) -> Tri (x < y) (x == y) (y < x)
  handle (yes x<y) (yes y<x) = bot-elim (asym-< {x} {y} x<y y<x)
  handle (yes x<y) (no y≮x)  = tri< x<y (\p -> y≮x (transport (\i -> (p i) < (p (~ i))) x<y)) y≮x
  handle (no x≮y)  (yes y<x) = tri> x≮y (\p -> x≮y (transport (\i -> (p (~ i)) < (p i)) y<x)) y<x
  handle (no x≮y)  (no y≮x)  = tri= x≮y (connected-< x≮y y≮x) y≮x


r+₁-preserves-order : (a b c : Rational) -> b < c -> (a r+ b) < (a r+ c)
r+₁-preserves-order a b c = subst Pos (sym path)
  where
  path : (a r+ c) r+ (r- (a r+ b)) == c r+ (r- b)
  path = cong2 _r+_ (r+-commute a c) (RationalRing.minus-distrib-plus {a} {b}) >=>
         r+-assoc c a ((r- a) r+ (r- b)) >=>
         cong (c r+_) (sym (r+-assoc a (r- a) (r- b)) >=>
                       (cong (_r+ (r- b)) (r+-inverse a)) >=>
                       (r+-left-zero (r- b)))

r--flips-order : (b c : Rational) -> b < c -> (r- b) > (r- c)
r--flips-order b c = subst Pos p
  where
  p : c r+ (r- b) == (r- b) r+ (r- (r- c))
  p = r+-commute c (r- b) >=> cong ((r- b) r+_) (sym (RationalRing.minus-double-inverse {c}))
