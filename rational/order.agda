{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order where

open import abs
open import base
open import equality
open import fraction.sign
open import hlevel
open import isomorphism
open import rational
open import rational.sign
open import relation
open import ring
open import ring.implementations.rational
open import semiring
open import set-quotient
open import sigma
open import sign
open import sign.instances.fraction
open import sign.instances.rational
open import truncation
open import univalence

import int.order
import int
import nat

open int using (Int ; int)
open nat using (ℕ ; Nat⁺; 2⁺ ; _*⁺_)

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


isSign'-self : (q : Rational') -> isSign (ℚ'->sign q) q
isSign'-self q = is-signℚ' (i.isSign-self (numer q i.* denom q))

_<'_ : Rational' -> Rational' -> Type₀
q <' r = Pos (r r+' (r-' q))

_>'_ : Rational' -> Rational' -> Type₀
q >' r = r <' q


_≤'_ : Rational' -> Rational' -> Type₀
q ≤' r = NonNeg (r r+' (r-' q))

_≥'_ : Rational' -> Rational' -> Type₀
q ≥' r = r ≤' q

isProp-<' : {q r : Rational'} -> isProp (q <' r)
isProp-<' = isProp-Pos _

isProp-≤' : {q r : Rational'} -> isProp (q ≤' r)
isProp-≤' = isProp-NonNeg _


r~-preserves-NonNeg : {q1 q2 : Rational'} -> NonNeg q1 -> q1 r~ q2 -> NonNeg q2
r~-preserves-NonNeg {q1} {q2} nn-q1 r = handle (ℚ'->sign q1) (isSign'-self q1)
  where
  handle : (s : Sign) -> isSign s q1 -> NonNeg q2
  handle pos-sign p-q1 = Pos->NonNeg (r~-preserves-sign p-q1 r)
  handle zero-sign z-q1 = Zero->NonNeg (r~-preserves-sign z-q1 r)
  handle neg-sign n-q1  = bot-elim (NonNeg->¬Neg nn-q1 n-q1)


r~-preserves-<₁ : {q1 q2 r : Rational'} -> q1 <' r -> q1 r~ q2 -> q2 <' r
r~-preserves-<₁ {q1} {q2} {r} q1<r q1~q2 =
  r~-preserves-sign q1<r (r+'-preserves-r~₂ r (r-' q1) (r-' q2) (r-'-preserves-r~ q1 q2 q1~q2))

r~-preserves-<₂ : {q r1 r2 : Rational'} -> q <' r1 -> r1 r~ r2 -> q <' r2
r~-preserves-<₂ {q} {r1} {r2} q<r1 r1~r2 =
  r~-preserves-sign q<r1 (r+'-preserves-r~₁ (r-' q) r1 r2 r1~r2)

private
  Pos->same-sign :
    (q : Rational') -> Pos q -> Σ[ s ∈ Sign ] (i.isSign s (numer q) × i.isSign s (denom q))
  Pos->same-sign q p = s1 , (i.isSign-self (numer q) ,
                      subst (\x -> i.isSign x (denom q)) (sym path) (i.isSign-self (denom q)))
    where
    s1 = i.int->sign (numer q)
    s2 = i.int->sign (denom q)
    path : s1 == s2
    path = handle s1 s2 (subst isPosSign i.int->sign-preserves-* (i.Pos->PosSign (isSignℚ'.v p)))
      where
      handle : (x y : Sign) -> isPosSign (x s* y) -> x == y
      handle pos-sign pos-sign _ = refl
      handle neg-sign neg-sign _ = refl
      handle pos-sign  zero-sign ()
      handle zero-sign zero-sign ()
      handle neg-sign  zero-sign ()

  same-sign->Pos :
    (q : Rational') -> (s : Sign) -> i.isSign s (numer q) -> i.isSign s (denom q) -> Pos q
  same-sign->Pos q s@pos-sign sn sd = is-signℚ' (int.*-isSign {s} {s} {numer q} {denom q} sn sd)
  same-sign->Pos q s@neg-sign sn sd = is-signℚ' (int.*-isSign {s} {s} {numer q} {denom q} sn sd)
  same-sign->Pos q zero-sign sn sd = bot-elim (int.NonZero->¬Zero (rNonZero q) sd)


r+'-preserves-Pos : {q1 q2 : Rational'} -> Pos q1 -> Pos q2 -> Pos (q1 r+' q2)
r+'-preserves-Pos {q1} {q2} p1 p2 = ans2
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

  ans2 : Pos (q1 r+' q2)
  ans2 = subst Pos (sym r+'-eval) (is-signℚ' ans)


r*'-preserves-Pos : {q1 q2 : Rational'} -> Pos q1 -> Pos q2 -> Pos (q1 r*' q2)
r*'-preserves-Pos {q1} {q2} p1 p2 = is-signℚ' ans
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

r1/'-preserves-Pos : (q : Rational') -> (i : ℚInv' q) -> Pos q -> Pos (r1/' q i)
r1/'-preserves-Pos q i p = is-signℚ' (subst i.Pos i.*-commute (isSignℚ'.v p))

r-'-flips-sign : (q : Rational') (s : Sign) -> (isSign s q) -> (isSign (s⁻¹ s) (r-' q))
r-'-flips-sign q s qs =
  is-signℚ'
    (subst (i.isSign (s⁻¹ s)) (sym i.minus-extract-left)
           (i.minus-isSign {numer q i.* denom q} {s} (isSignℚ'.v qs)))

Zero-0r' : Zero 0r'
Zero-0r' = is-signℚ' (subst i.Zero (sym i.*-left-zero) tt)

Zero-r~ : (q : Rational') -> Zero q -> q r~ 0r'
Zero-r~ q zq = (cong (i._* (denom 0r')) path >=> i.*-left-zero >=> sym i.*-left-zero)
  where
  path : (numer q) == (i.int 0)
  path = i.*-left-zero-eq (rNonZero q) (i.Zero-path ((numer q) i.* (denom q)) (isSignℚ'.v zq))

irrefl-<' : Irreflexive _<'_
irrefl-<' {a} a<a = (i.NonPos->¬Pos (i.Zero->NonPos (isSignℚ'.v b-zero)) (isSignℚ'.v b-pos))
  where
  b = a r+' (r-' a)

  b-pos : Pos b
  b-pos = a<a
  b-zero : Zero b
  b-zero = r~-preserves-sign {0r'} {b} {zero-sign} Zero-0r' (sym (r+'-inverse a))

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
  a<c = r~-preserves-sign {e r+' d} {f} {s = pos-sign} (r+'-preserves-Pos b<c a<b) f-path


decide-<' : Decidable2 _<'_
decide-<' x y = handle (i.int->sign z') (i.isSign-self z')
  where
  z = y r+' (r-' x)
  z' = numer z i.* denom z
  handle : (s : Sign) -> (i.isSign s z') -> Dec (x <' y)
  handle pos-sign pz = yes (is-signℚ' pz)
  handle zero-sign zz = no (\ pz -> i.NonPos->¬Pos (i.Zero->NonPos zz) (isSignℚ'.v pz))
  handle neg-sign nz = no (\ pz -> i.NonPos->¬Pos (i.Neg->NonPos nz) (isSignℚ'.v pz))




private
  Dense : {ℓ ℓA : Level} {A : Type ℓA} -> Rel A ℓ -> Type (ℓ-max ℓA ℓ)
  Dense {A = A} _<_ = {x y : A} -> x < y -> Σ[ z ∈ A ] (x < z × z < y)



ℚ->sign : Rational -> Sign
ℚ->sign = RationalElim.rec isSet-Sign ℚ'->sign preserved
  where
  preserved : (q1 q2 : Rational') -> (q1 r~ q2) -> (ℚ'->sign q1) == (ℚ'->sign q2)
  preserved q1 q2 r =
    isSign-unique q2 _ _
      (r~-preserves-sign {q1} {q2} {ℚ'->sign q1} (isSign'-self q1) r)
      (isSign'-self q2)

isSign-self : (q : Rational) -> isSignℚ (ℚ->sign q) q
isSign-self =
  RationalElim.elimProp
    (\q -> isProp-isSignℚ (ℚ->sign q) q)
    (\q -> is-signℚ (isSign'-self q))


Posℚ : Rational -> Type₀
Posℚ = isSignℚ pos-sign
Negℚ : Rational -> Type₀
Negℚ = isSignℚ neg-sign
Zeroℚ : Rational -> Type₀
Zeroℚ = isSignℚ zero-sign

isProp-Posℚ : {r : Rational} -> isProp (Posℚ r)
isProp-Posℚ {r} = isProp-isSignℚ pos-sign r

ℚ⁺ : Type₀
ℚ⁺ = Σ ℚ Posℚ
ℚ⁻ : Type₀
ℚ⁻ = Σ ℚ Negℚ

Zero-0r : Zero 0r
Zero-0r = is-signℚ Zero-0r'

Zero-path : (q : Rational) -> Zeroℚ q -> q == 0r
Zero-path =
  RationalElim.elimProp
    (\_ -> isPropΠ (\_ -> isSetRational _ _))
    (\q zq -> eq/ _ _ (Zero-r~ q (isSignℚ.v zq)))

-- DO STUFF
r+-preserves-Pos : (q1 q2 : Rational) -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r+ q2)
r+-preserves-Pos =
  RationalElim.elimProp2
    {C2 = \q1 q2 -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r+ q2)}
    (\q1 q2 -> isPropΠ2 (\ _ _ -> isProp-isSignℚ pos-sign (q1 r+ q2)))
    (\q1 q2 p1 p2 -> is-signℚ (r+'-preserves-Pos (isSignℚ.v p1) (isSignℚ.v p2)))

r*-preserves-Pos : (q1 q2 : Rational) -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r* q2)
r*-preserves-Pos =
  RationalElim.elimProp2
    {C2 = \q1 q2 -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r* q2)}
    (\q1 q2 -> isPropΠ2 (\ _ _ -> isProp-isSignℚ pos-sign (q1 r* q2)))
    (\q1 q2 p1 p2 -> is-signℚ (r*'-preserves-Pos (isSignℚ.v p1) (isSignℚ.v p2)))

r--flips-sign : (q : Rational) (s : Sign) -> (isSignℚ s q) -> (isSignℚ (s⁻¹ s) (r- q))
r--flips-sign =
  RationalElim.elimProp
    (\q -> isPropΠ2 (\ s _ -> isProp-isSignℚ (s⁻¹ s) (r- q)))
    (\q s qs -> is-signℚ (r-'-flips-sign q s (isSignℚ.v qs)))

r1/-preserves-Pos : (q : Rational) -> (i : ℚInv q) -> Pos q -> Pos (r1/ q i)
r1/-preserves-Pos =
  RationalElim.elimProp
    (\q -> isPropΠ2 (\ i _ -> isProp-Pos (r1/ q i)))
    (\q i p -> is-signℚ (r1/'-preserves-Pos q (ℚInv->ℚInv' q i) (isSignℚ.v p)))


_<_ : Rational -> Rational -> Type₀
q < r = Posℚ (r r+ (r- q))

_>_ : Rational -> Rational -> Type₀
q > r = r < q

isProp-< : {a b : Rational} -> isProp (a < b)
isProp-< {a} {b} = isProp-isSignℚ pos-sign (b r+ (r- a))

irrefl-< : Irreflexive _<_
irrefl-< {a} a<a =
  RationalElim.elimProp
    {C = (\r -> r < r -> Bot)}
    (\_ -> isPropΠ (\_ -> isPropBot))
    (\r s -> irrefl-<' {r} (isSignℚ.v s)) a a<a

trans-< : Transitive _<_
trans-< {a} {b} {c} a<b b<c =
  RationalElim.elimProp3
    {C3 = (\a b c -> a < b -> b < c -> a < c)}
    (\a _ c -> isPropΠ2 (\_ _ -> isProp-< {a} {c}))
    (\a b c a<b b<c -> is-signℚ (trans-<' (isSignℚ.v a<b) (isSignℚ.v b<c))) a b c a<b b<c

asym-< : Asymmetric _<_
asym-< {a} {b} lt1 lt2 = irrefl-< {a} (trans-< {a} {b} {a} lt1 lt2)

Pos-1/ℕ : (n : Nat⁺) -> Posℚ (1/ℕ n)
Pos-1/ℕ (n@(suc _) , _) = is-signℚ (is-signℚ' (i.*-Pos-Pos tt tt))

Pos-0< : (q : Rational) -> Posℚ q -> 0r < q
Pos-0< q = subst Posℚ p
  where
  p : q == q r+ (r- 0r)
  p = sym (r+-right-zero q)

Pos-1r : Posℚ 1r
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

  pos-d1 : Posℚ d1
  pos-d1 = lt

  pos-d2 : Posℚ d2
  pos-d2 = r*-preserves-Pos d1 1/2r pos-d1 (Pos-1/ℕ (2 , tt))

  d3-path : d2 == d3
  d3-path =
    sym (cong (_r+ (r- x)) (r+-commute x d2) >=>
         r+-assoc d2 x (r- x) >=>
         cong (d2 r+_) (r+-inverse x) >=>
         r+-right-zero d2)
  pos-d3 : Posℚ d3
  pos-d3 = subst Posℚ d3-path pos-d2

  d4-path : d2 == d4
  d4-path =
    sym (cong (\z -> y r+ (r- z)) z-path >=>
         cong (y r+_) (RationalRing.minus-distrib-plus {y} {r- d2}) >=>
         sym (r+-assoc y (r- y) (r- (r- d2))) >=>
         cong2 _r+_ (r+-inverse y) (RationalRing.minus-double-inverse {d2}) >=>
         r+-left-zero d2)
  pos-d4 : Posℚ d4
  pos-d4 = subst Posℚ d4-path pos-d2


decide-< : Decidable2 _<_
decide-< =
  RationalElim.elimProp2
    (\a b -> isPropDec (isProp-< {a} {b}))
    (\a b -> handle (decide-<' a b))
  where
  handle : {q : Rational'} -> Dec (Pos q) -> Dec (Pos [ q ])
  handle (yes pq) = yes (is-signℚ pq)
  handle (no ¬pq) = no (\v -> ¬pq (isSignℚ.v v))

private
  zero-diff->path : (x y : Rational) -> Zeroℚ (y r+ (r- x)) -> x == y
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

  handle : (s : Sign) -> isSignℚ s z -> x == y
  handle pos-sign pz = bot-elim (x≮y pz)
  handle zero-sign zz = zero-diff->path x y zz
  handle neg-sign nz = bot-elim (y≮x (subst Posℚ p (r--flips-sign z neg-sign nz)))

trichotomous-< : Trichotomous _<_
trichotomous-< x y = handle (decide-< x y) (decide-< y x)
  where
  handle : Dec (x < y) -> Dec (y < x) -> Tri (x < y) (x == y) (y < x)
  handle (yes x<y) (yes y<x) = bot-elim (asym-< {x} {y} x<y y<x)
  handle (yes x<y) (no y≮x)  = tri< x<y (\p -> y≮x (transport (\i -> (p i) < (p (~ i))) x<y)) y≮x
  handle (no x≮y)  (yes y<x) = tri> x≮y (\p -> x≮y (transport (\i -> (p (~ i)) < (p i)) y<x)) y<x
  handle (no x≮y)  (no y≮x)  = tri= x≮y (connected-< x≮y y≮x) y≮x

comparison-< : Comparison _<_
comparison-< x y z x<z = handle (trichotomous-< y w)
  where
  Σw = dense-< {x} {z} x<z
  w = fst Σw
  x<w = proj₁ (snd Σw)
  w<z = proj₂ (snd Σw)
  handle : Tri (y < w) (y == w) (y > w) -> ∥ (x < y) ⊎ (y < z) ∥
  handle (tri< y<w _ _)  = ∣ inj-r (trans-< {y} {w} {z} y<w w<z) ∣
  handle (tri= _ y==w _) = ∣ inj-l (subst (x <_) (sym y==w) x<w) ∣
  handle (tri> _ _ w<y)  = ∣ inj-l (trans-< {x} {w} {y} x<w w<y) ∣



r+₁-preserves-order : (a b c : Rational) -> b < c -> (a r+ b) < (a r+ c)
r+₁-preserves-order a b c = subst Posℚ (sym path)
  where
  path : (a r+ c) r+ (r- (a r+ b)) == c r+ (r- b)
  path = cong2 _r+_ (r+-commute a c) (RationalRing.minus-distrib-plus {a} {b}) >=>
         r+-assoc c a ((r- a) r+ (r- b)) >=>
         cong (c r+_) (sym (r+-assoc a (r- a) (r- b)) >=>
                       (cong (_r+ (r- b)) (r+-inverse a)) >=>
                       (r+-left-zero (r- b)))

r+₂-preserves-order : (a b c : Rational) -> a < b -> (a r+ c) < (b r+ c)
r+₂-preserves-order a b c lt =
  subst2 _<_ (r+-commute c a) (r+-commute c b) (r+₁-preserves-order c a b lt)


r--flips-order : (b c : Rational) -> b < c -> (r- b) > (r- c)
r--flips-order b c = subst Posℚ p
  where
  p : c r+ (r- b) == (r- b) r+ (r- (r- c))
  p = r+-commute c (r- b) >=> cong ((r- b) r+_) (sym (RationalRing.minus-double-inverse {c}))

r+-Pos->order : (a : ℚ) (b : Σ ℚ Posℚ) -> a < (a r+ ⟨ b ⟩)
r+-Pos->order a (b , pos-b) = subst Posℚ (sym path) pos-b
  where
  path : (a r+ b) r+ (r- a) == b
  path = (cong (_r+ (r- a)) (r+-commute a b))
         >=> r+-assoc b a (r- a)
         >=> (cong (b r+_) (r+-inverse a))
         >=> r+-right-zero b

r+-Neg->order : (a : ℚ) (b : Σ ℚ Negℚ) -> a > (a r+ ⟨ b ⟩)
r+-Neg->order a (b , neg-b) = subst ((a r+ b) <_) path lt
  where
  lt : (a r+ b) < ((a r+ b) r+ (r- b))
  lt = r+-Pos->order (a r+ b) (r- b , r--flips-sign b neg-sign neg-b)
  path : ((a r+ b) r+ (r- b)) == a
  path = r+-assoc a b (r- b) >=> cong (a r+_) (r+-inverse b) >=> r+-right-zero a

r*₁-preserves-order : (a : ℚ⁺) (b c : Rational) -> b < c -> (⟨ a ⟩ r* b) < (⟨ a ⟩ r* c)
r*₁-preserves-order (a , pos-a) b c b<c = subst Posℚ path pos-diff
  where
  pos-diff : Posℚ (a r* (c r+ (r- b)))
  pos-diff = r*-preserves-Pos a (c r+ (r- b)) pos-a b<c

  path : (a r* (c r+ (r- b))) == (a r* c) r+ (r- (a r* b))
  path = *-distrib-+-left {_} {_} {a} {c} {r- b} >=>
         cong ((a r* c) r+_) (RationalRing.minus-extract-right {a} {b})

r*₂-preserves-order : (a b : Rational) (c : ℚ⁺) -> a < b -> ( a r* ⟨ c ⟩) < (b r* ⟨ c ⟩)
r*₂-preserves-order a b c@(c' , _) a<b =
  subst2 _<_ (r*-commute c' a) (r*-commute c' b) (r*₁-preserves-order c a b a<b)


1/2r<1r : 1/2r < 1r
1/2r<1r = subst2 _<_ (r+-left-zero 1/2r) (2r-path 1/2r >=> 2r-1/2r-path)  0r+1/2r<1/2r+1/2r
  where
  0<1/2r : 0r < 1/2r
  0<1/2r = Pos-0< 1/2r (Pos-1/ℕ (2 , tt))

  0r+1/2r<1/2r+1/2r : (0r r+ 1/2r) < (1/2r r+ 1/2r)
  0r+1/2r<1/2r+1/2r = r+₂-preserves-order 0r 1/2r 1/2r 0<1/2r

1/2ℕ<1/ℕ : (n : Nat⁺) -> 1/ℕ (2⁺ *⁺ n) < 1/ℕ n
1/2ℕ<1/ℕ n =
  subst2 _<_ (sym (1/2ℕ-path n)) (r*-left-one (1/ℕ n))
        (r*₂-preserves-order 1/2r 1r (1/ℕ n , Pos-1/ℕ n) 1/2r<1r)

ℕ->ℚ'-preserves-order : (a b : Nat) -> a nat.< b -> (ℕ->ℚ' a) <' (ℕ->ℚ' b)
ℕ->ℚ'-preserves-order a b (c , path) = ans
  where

  sd : Rational'
  sd = (same-denom-r+' (ℕ->ℚ' b) (r-' (ℕ->ℚ' a)))

  diff : Rational'
  diff = (ℕ->ℚ' b r+' (r-' (ℕ->ℚ' a)))

  sd~diff : sd r~ diff
  sd~diff = same-denom-r+'-r~ (ℕ->ℚ' b) (r-' (ℕ->ℚ' a)) refl

  path2 : int (c nat.+' suc a) i.+ (i.- (int a)) == i.pos c
  path2 = i.+-left (cong int nat.+'-right-suc) >=>
          i.+-left (int-inject-+' {suc c} {a}) >=>
          i.+-assoc >=>
          i.+-right i.add-minus-zero >=>
          i.+-right-zero

  Pos-b-a : i.Pos ((int b) i.+ (i.- (int a)))
  Pos-b-a = subst i.Pos (sym path2 >=> cong (\x -> (int x i.+ (i.- (int a)))) path) tt

  Pos-sd : Pos sd
  Pos-sd = is-signℚ' (int.*-Pos-Pos Pos-b-a tt)

  ans : Pos diff
  ans = r~-preserves-sign Pos-sd sd~diff

ℕ->ℚ-preserves-order : (a b : Nat) -> a nat.< b -> (ℕ->ℚ a) < (ℕ->ℚ b)
ℕ->ℚ-preserves-order a b a<b = is-signℚ (ℕ->ℚ'-preserves-order a b a<b)

1/ℕ-flips-order : (a b : Nat⁺) -> ⟨ a ⟩ nat.< ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
1/ℕ-flips-order a@(a' , _) b@(b' , _) lt = subst2 _<_ b-path a-path ab*<
  where
  ab = 1/ℕ a r* 1/ℕ b
  pos-ab : Pos ab
  pos-ab = r*-preserves-Pos _ _ (Pos-1/ℕ a) (Pos-1/ℕ b)

  a-path : (ab r* (ℕ->ℚ b')) == 1/ℕ a
  a-path =
    r*-assoc (1/ℕ a) (1/ℕ b) (ℕ->ℚ b') >=>
    cong (1/ℕ a r*_) (1/ℕ-ℕ-path b) >=>
    r*-right-one (1/ℕ a)
  b-path : (ab r* (ℕ->ℚ a')) == 1/ℕ b
  b-path =
    cong (_r* ℕ->ℚ a') (r*-commute (1/ℕ a) (1/ℕ b)) >=>
    r*-assoc (1/ℕ b) (1/ℕ a) (ℕ->ℚ a') >=>
    cong (1/ℕ b r*_) (1/ℕ-ℕ-path a) >=>
    r*-right-one (1/ℕ b)

  ab*< : (ab r* (ℕ->ℚ a')) < (ab r* (ℕ->ℚ b'))
  ab*< = r*₁-preserves-order (ab , pos-ab) (ℕ->ℚ a') (ℕ->ℚ b')
           (ℕ->ℚ-preserves-order a' b' lt)


-- ℕ<-1/ℕ< : (a b : Nat⁺) -> ⟨ a ⟩ nat.< ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
-- ℕ<-1/ℕ< a b lt = ?

-- min and max

minℚ : ℚ -> ℚ -> ℚ
minℚ x y = case (decide-< x y) of (\
  { (yes _) -> x
  ; (no _) -> y
  })

private
  maxℚ-helper : (x y : ℚ) -> Tri (x < y) (x == y) (x > y) -> ℚ
  maxℚ-helper x y (tri< _ _ _) = y
  maxℚ-helper x y (tri= _ _ _) = x
  maxℚ-helper x y (tri> _ _ _) = x


maxℚ : ℚ -> ℚ -> ℚ
maxℚ x y = maxℚ-helper x y (trichotomous-< x y)

absℚ : ℚ -> ℚ
absℚ x = maxℚ x (r- x)


diffℚ : ℚ -> ℚ -> ℚ
diffℚ x y = (y r+ (r- x))

diffℚ-anticommute : (x y : ℚ) -> diffℚ x y == r- (diffℚ y x)
diffℚ-anticommute x y = sym (
  RationalRing.minus-distrib-plus {x} {r- y} >=>
  cong ((r- x) r+_) (RationalRing.minus-double-inverse {y}) >=>
  r+-commute (r- x) y)

r+-swap-diffℚ : (a b c d : Rational) -> ((diffℚ a b) r+ (diffℚ c d)) == (diffℚ (a r+ c) (b r+ d))
r+-swap-diffℚ a b c d =
  r+-assoc b (r- a) (diffℚ c d) >=>
  cong (b r+_) (sym (r+-assoc (r- a) d (r- c)) >=>
                cong (_r+ (r- c)) (r+-commute (r- a) d) >=>
                r+-assoc d (r- a) (r- c) >=>
                cong (d r+_) (sym (RationalRing.minus-distrib-plus {a} {c}))) >=>
  sym (r+-assoc b d (r- (a r+ c)))


diffℚ-trans : (x y z : ℚ) -> diffℚ x y r+ diffℚ y z == (diffℚ x z)
diffℚ-trans x y z =
  r+-commute (diffℚ x y) (diffℚ y z) >=>
  r+-assoc z (r- y) (diffℚ x y) >=>
  cong (z r+_) (sym (r+-assoc (r- y) y (r- x)) >=>
                cong (_r+ (r- x)) (r+-commute (r- y) y >=> r+-inverse y) >=>
                r+-left-zero (r- x))

diffℚ-step : (x y : ℚ) -> x + diffℚ x y == y
diffℚ-step x y =
  sym (r+-assoc x y (r- x)) >=>
  cong (_r+ (r- x)) (r+-commute x y) >=>
  (r+-assoc y x (r- x)) >=>
  cong (y r+_) (r+-inverse x) >=>
  r+-right-zero y


abs-diffℚ : ℚ -> ℚ -> ℚ
abs-diffℚ x y = absℚ (diffℚ x y)

midℚ : ℚ -> ℚ -> ℚ
midℚ x y = 1/2r r* (x r+ y)

maxℚ-weaken-<₁ : (x y z : ℚ) -> (maxℚ x y < z) -> x < z
maxℚ-weaken-<₁ x y z lt = handle (trichotomous-< x y) (maxℚ x y) refl lt
  where
  handle : (t : Tri (x < y) (x == y) (x > y)) -> (w : ℚ) -> (w == maxℚ-helper x y t) -> w < z
           -> x < z
  handle (tri< x<y  _ _) w p w<z = trans-< {x} {y} {z} x<y (subst (_< z) p w<z)
  handle (tri= _ _ _) w p w<z = (subst (_< z) p w<z)
  handle (tri> _ _ _) w p w<z = (subst (_< z) p w<z)

r+-both-preserves-order : (a b c d : Rational) -> a < b -> c < d -> (a r+ c) < (b r+ d)
r+-both-preserves-order a b c d a<b c<d = subst Posℚ (r+-swap-diffℚ a b c d) Pos-sum-diff
  where
  Pos-sum-diff : Posℚ ((diffℚ a b) r+ (diffℚ c d))
  Pos-sum-diff = r+-preserves-Pos (diffℚ a b) (diffℚ c d) a<b c<d


-- floor and <


_ℚ≤_ : ℚ -> ℚ -> Type₀
x ℚ≤ y = NonNeg (diffℚ x y)

ℚ' = Rational'


isProp-ℚ≤ : {x y : ℚ} -> isProp (x ℚ≤ y)
isProp-ℚ≤ {x} {y} = isProp-NonNeg (diffℚ x y)

split-< : (q r : ℚ) -> (q < r) ⊎ (r ℚ≤ q)
split-< q r = handle (trichotomous-< q r)
  where
  handle : Tri (q < r) (q == r) (q > r) -> (q < r) ⊎ (r ℚ≤ q)
  handle (tri< q<r _ _) = inj-l q<r
  handle (tri= _ q=r _) =
    inj-r (inj-r (subst Zero (sym (r+-inverse r) >=> cong (_r+ (r- r)) (sym q=r)) Zero-0r))
  handle (tri> _ _ q>r) =
    inj-r (inj-l q>r)




NonNeg-fractional-part' : (q : ℚ') -> NonNeg (fractional-part' q)
NonNeg-fractional-part' (record { numerator = n ; denominator = d@(int.pos d')}) =
  NonNeg-nd->ℚ' (int.*-NonNeg-Pos (remainderℤ-NonNeg n (d , inj-l tt) tt) tt)
NonNeg-fractional-part' (record { numerator = n ; denominator = d@(int.neg d')}) =
  NonNeg-nd->ℚ' (int.*-NonPos-Neg (remainderℤ-NonPos n (d , inj-r tt) tt) tt)
NonNeg-fractional-part' (record { denominator = int.zero-int ; NonZero-denominator = inj-l ()})
NonNeg-fractional-part' (record { denominator = int.zero-int ; NonZero-denominator = inj-r ()})

NonNeg-fractional-part : (q : ℚ) -> NonNeg (fractional-part q)
NonNeg-fractional-part =
  RationalElim.elimProp
    (\q -> isProp-NonNeg (fractional-part q))
    (\q -> NonNeg-ℚ'->ℚ (NonNeg-fractional-part' q))

NonNeg->0≤ : (q : ℚ) -> NonNeg q -> 0r ℚ≤ q
NonNeg->0≤ q nn-q = subst NonNeg (sym (r+-right-zero q)) nn-q

diffℚ-fractional-part : (q : Rational) -> diffℚ (floorℚ q) q == (fractional-part q)
diffℚ-fractional-part q =
  cong (_r+ (r- (floorℚ q))) (sym (fractional-part-r+ q) >=>
                              r+-commute (floorℚ q) (fractional-part q)) >=>
  r+-assoc (fractional-part q) (floorℚ q) (r- (floorℚ q)) >=>
  cong (fractional-part q r+_) (r+-inverse (floorℚ q)) >=>
  r+-right-zero (fractional-part q)

floor-≤ : (q : ℚ) -> (floorℚ q) ℚ≤ q
floor-≤ q = subst NonNeg (sym (diffℚ-fractional-part q)) (NonNeg-fractional-part q)

fractional-part-0≤ : (q : ℚ) -> 0r ℚ≤ (fractional-part q)
fractional-part-0≤ q = NonNeg->0≤ (fractional-part q) (NonNeg-fractional-part q)



r+-Pos-NonNeg : {q1 q2 : Rational} -> Pos q1 -> NonNeg q2 -> Pos (q1 r+ q2)
r+-Pos-NonNeg {q1} {q2} p-q1 (inj-l p-q2) =
  r+-preserves-Pos q1 q2 p-q1 p-q2
r+-Pos-NonNeg {q1} {q2} p-q1 (inj-r z-q2) =
  subst Pos (sym (r+-right-zero q1) >=> cong (q1 r+_) (sym (Zero-path q2 z-q2))) p-q1

r+-NonNeg-Pos : {q1 q2 : Rational} -> NonNeg q1 -> Pos q2 -> Pos (q1 r+ q2)
r+-NonNeg-Pos {q1} {q2} n p = subst Pos (r+-commute q2 q1) (r+-Pos-NonNeg p n)

trans-<-≤ : {q1 q2 q3 : Rational} -> q1 < q2 -> q2 ℚ≤ q3 -> q1 < q3
trans-<-≤ {q1} {q2} {q3} q1<q2 q2≤q3 =
  subst Pos (diffℚ-trans q1 q2 q3) (r+-Pos-NonNeg q1<q2 q2≤q3)

trans-≤-< : {q1 q2 q3 : Rational} -> q1 ℚ≤ q2 -> q2 < q3 -> q1 < q3
trans-≤-< {q1} {q2} {q3} q1≤q2 q2<q3 =
  subst Pos (diffℚ-trans q1 q2 q3) (r+-NonNeg-Pos q1≤q2 q2<q3)



-- Archimedean


private
  nd⁺->ℚ' : (n : Nat) (d : Nat⁺) -> ℚ'
  nd⁺->ℚ' n (d , pos-d) = record
    { numerator = i.ℕ->ℤ n
    ; denominator = i.ℕ->ℤ d
    ; NonZero-denominator = i.Pos->NonZero (i.Pos'->Pos pos-d)
    }

  n⁺d⁺->ℚ' : (n d : Nat⁺) -> ℚ'
  n⁺d⁺->ℚ' (n' , _)  d = nd⁺->ℚ' n' d

  n⁺d⁺->ℚ : (n d : Nat⁺) -> ℚ
  n⁺d⁺->ℚ n d = [ n⁺d⁺->ℚ' n d ]

  n⁺d⁺->ℚ⁺ : (n d : Nat⁺) -> ℚ⁺
  n⁺d⁺->ℚ⁺ n d = n⁺d⁺->ℚ n d ,
           is-signℚ (is-signℚ' (i.*-Pos-Pos (i.Pos'->Pos (snd n)) (i.Pos'->Pos (snd d))))


  ℚ⁺-elimProp :
    {ℓ : Level} -> {P : Pred ℚ⁺ ℓ} -> ((q : ℚ⁺) -> isProp (P q)) ->
    ((n d : Nat⁺) -> P (n⁺d⁺->ℚ⁺ n d)) ->
    (q : ℚ⁺) -> P q
  ℚ⁺-elimProp {P = P} isProp-P f (q , pos-q) =
    RationalElim.elimProp (\q -> isPropΠ (\pos-q -> isProp-P (q , pos-q))) handle q pos-q
    where
    find-rep : (q' : ℚ') -> (Pos q') -> Σ[ n ∈ Nat⁺ ] (Σ[ d ∈ Nat⁺ ] (n⁺d⁺->ℚ' n d r~ q'))
    find-rep (record { numerator = (i.pos n') ; denominator = (i.pos d') }) _ =
      ((suc n' , tt) , (suc d' , tt) , refl)
    find-rep (record { numerator = (i.zero-int) ; denominator = (i.pos d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg (inj-r tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.neg _) ; denominator = (i.pos d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg (inj-l tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.pos _) ; denominator = (i.neg d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonNeg-NonPos (inj-l tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.zero-int) ; denominator = (i.neg d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonNeg-NonPos (inj-r tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.neg n') ; denominator = (i.neg d') }) _ =
      ((suc n' , tt) , (suc d' , tt) , i.minus-extract-right >=> sym i.minus-extract-left )
    find-rep (record { denominator = i.zero-int ; NonZero-denominator = inj-l ()})
    find-rep (record { denominator = i.zero-int ; NonZero-denominator = inj-r ()})

    handle : (q' : ℚ') -> (pos-q : (Pos [ q' ])) -> P ([ q' ] , pos-q)
    handle q' pos-q' = subst P path (f n d)
      where
      rep = find-rep q' (isSignℚ.v pos-q')
      n = fst rep
      d = fst (snd rep)
      nd~ = snd (snd rep)

      path : (n⁺d⁺->ℚ⁺ n d) == ([ q' ] , pos-q')
      path = ΣProp-path (\{x} -> isProp-Posℚ {x}) (eq/ _ _ nd~)


  1/ℕ-<-step1 : (n d : Nat⁺) -> (1/ℕ' d) ≤' (n⁺d⁺->ℚ' n d)
  1/ℕ-<-step1 n@(n'@(suc n'') , _)  d@(d' , pos-d) = ans
    where
    x1 = same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d))
    x2 = ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))

    NonNeg-numer : i.NonNeg (int n' i.+ (i.- (int 1)))
    NonNeg-numer = subst i.NonNeg (sym i.+-eval >=> i.+-commute) (int.NonNeg-nonneg n'')

    ans2 : NonNeg (same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)))
    ans2 = NonNeg-nd->ℚ' (i.*-NonNeg-NonNeg NonNeg-numer (i.Pos->NonNeg (i.Pos'->Pos pos-d)))

    ans~ : same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)) r~ ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))
    ans~ = same-denom-r+'-r~ (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)) refl

    ans : NonNeg ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))
    ans = r~-preserves-NonNeg {x1} {x2} ans2 ans~


  1/ℕ-<-step2 : (n d : Nat⁺) -> ∃[ m ∈ Nat⁺ ] ( 1/ℕ' m ≤' (n⁺d⁺->ℚ' n d))
  1/ℕ-<-step2 n d = ∣ d , 1/ℕ-<-step1 n d ∣

  1/ℕ-<-step3 : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ ⟨ q ⟩)
  1/ℕ-<-step3 = ℚ⁺-elimProp (\q -> squash) (\n d -> (∥-map (handle n d) (1/ℕ-<-step2 n d)))
    where
    handle : (n d : Nat⁺) -> Σ[ m ∈ Nat⁺ ] (1/ℕ' m ≤' (n⁺d⁺->ℚ' n d)) ->
             Σ[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ (n⁺d⁺->ℚ n d))
    handle n d (m , p) = m , NonNeg-ℚ'->ℚ p

small-1/ℕ : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m < ⟨ q ⟩)
small-1/ℕ q = ∥-map handle (1/ℕ-<-step3 q)
  where
  handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ ⟨ q ⟩) -> Σ[ m ∈ Nat⁺ ] (1/ℕ m < ⟨ q ⟩)
  handle (m , m≤) = (2⁺ *⁺ m) , trans-<-≤ {1/ℕ (2⁺ *⁺ m)} {1/ℕ m} {⟨ q ⟩} (1/2ℕ<1/ℕ m) m≤

private
  small-1/2^ℕ-step1 : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < ⟨ q ⟩)
  small-1/2^ℕ-step1 q@(q' , _) = ∥-map handle (small-1/ℕ q)
    where
    handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m < q') -> Σ[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < q')
    handle (m@(m' , _) , lt) =
      m , trans-< {1/ℕ (2⁺ nat.^⁺ m')} {1/ℕ m} {q'}
            (1/ℕ-flips-order m (2⁺ nat.^⁺ m') (nat.2^n-large m')) lt

small-1/2^ℕ : (q : ℚ⁺) -> ∃[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < ⟨ q ⟩)
small-1/2^ℕ q@(q' , _) = ∥-map handle (small-1/2^ℕ-step1 q)
  where
  handle : Σ[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < q') ->
           Σ[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < q')
  handle ((m , _) , lt) = m , subst (_< q') (1/2^ℕ-path m) lt


ℚ-archimedian : (q1 q2 : ℚ⁺) -> ∃[ n ∈ Nat ] (((1/2r r^ℕ⁰ n) r* ⟨ q1 ⟩) < ⟨ q2 ⟩)
ℚ-archimedian q1@(q1' , pos-q1) q2@(q2' , pos-q2) = ∥-map handle (small-1/2^ℕ q3)
  where
  iq1 : ℚInv q1'
  iq1 p = (NonZero->¬Zero (Pos->NonZero pos-q1) (subst Zero (sym p) Zero-0r))

  q3' = q2' r* (r1/ q1' iq1)
  q3 : ℚ⁺
  q3 = q3' , r*-preserves-Pos _ _ pos-q2 (r1/-preserves-Pos q1' iq1 pos-q1)

  q3-path : q3' r* q1' == q2'
  q3-path = r*-assoc q2' (r1/ q1' iq1) q1' >=>
            cong (q2' r*_) (r1/-inverse q1' iq1) >=>
            r*-right-one q2'

  handle : Σ[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < q3') ->
           Σ[ m ∈ Nat ] (((1/2r r^ℕ⁰ m) r* q1') < q2')
  handle (m , lt) = m , subst (((1/2r r^ℕ⁰ m) r* q1') <_) q3-path lt2
    where
    lt2 : ((1/2r r^ℕ⁰ m) r* q1') < (q3' r* q1')
    lt2 = r*₂-preserves-order (1/2r r^ℕ⁰ m) q3' q1 lt


-- Seperate

seperate-< : (a b : ℚ) -> a < b -> Σ[ ε ∈ ℚ⁺ ] (a r+ ⟨ ε ⟩) < (b r+ (r- ⟨ ε ⟩))
seperate-< a b a<b = ε , pos-diff
  where
  Pos-1/2r = Pos-1/ℕ 2⁺
  ε' = 1/2r r* (1/2r r* (diffℚ a b))
  ε : ℚ⁺
  ε = ε' , r*-preserves-Pos 1/2r _ Pos-1/2r (r*-preserves-Pos 1/2r (diffℚ a b) Pos-1/2r a<b)

  path : (diffℚ (a r+ ε') (b r+ (r- ε'))) == 1/2r r* (diffℚ a b)
  path =
    sym (r+-swap-diffℚ a b ε' (r- ε')) >=>
    cong2 _r+_
          (sym (r*-left-one (diffℚ a b)))
          (sym (RationalRing.minus-distrib-plus {ε'} {ε'}) >=>
           cong r-_ (1/2r-path' (1/2r r* (diffℚ a b))) >=>
           sym (RationalRing.minus-extract-left {1/2r} {diffℚ a b})) >=>
    sym (*-distrib-+-right {_} {_} {1r} {r- 1/2r} {diffℚ a b}) >=>
    cong (_r* (diffℚ a b)) (cong (_r+ (r- 1/2r)) (sym (1/2r-path 1r) >=>
                                                  cong2 _+_ (r*-left-one 1/2r) (r*-left-one 1/2r)) >=>
                            r+-assoc 1/2r 1/2r (r- 1/2r) >=>
                            diffℚ-step 1/2r 1/2r)

  pos-diff : Pos (diffℚ (a r+ ε') (b r+ (r- ε')))
  pos-diff = subst Pos (sym path) (r*-preserves-Pos 1/2r (diffℚ a b) (Pos-1/ℕ 2⁺) a<b)
