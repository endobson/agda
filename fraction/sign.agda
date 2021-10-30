{-# OPTIONS --cubical --safe --exact-split #-}

module fraction.sign where

open import additive-group
open import additive-group.instances.int
open import base
open import equality
open import hlevel.base
open import nat
open import rational
open import ring.implementations
open import semiring
open import sign
open import sign.instances.int

import int.order

open import int using
  ( Int
  ; ℤ
  ; *-Pos-Pos
  ; *-Pos-Neg
  ; *-Neg-Pos
  ; *-Neg-Neg
  ; +-Pos-Pos
  ; +-Neg-Neg
  )

private
  module i where
    open int.order public
    open int public

private
  numer : Rational' -> Int
  numer = Rational'.numerator
  denom : Rational' -> Int
  denom = Rational'.denominator
  rNonZero : (r : Rational') -> NonZero (denom r)
  rNonZero = Rational'.NonZero-denominator

record isSignℚ' (s : Sign) (q : Rational') : Type₀ where
  constructor is-signℚ'
  field
    v : isSign s (numer q * denom q)

private
  abstract
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

private
  abstract
    ℚ'->sign : Rational' -> Sign
    ℚ'->sign q = sign (numer q * denom q)

    isSign'-self : (q : Rational') -> isSign (ℚ'->sign q) q
    isSign'-self q = is-signℚ' (i.isSign-self (numer q * denom q))

instance
  DecidableSignStr-ℚ' : DecidableSignStr SignStr-ℚ'
  DecidableSignStr-ℚ' = record
    { decide-sign = \q -> _ , isSign'-self q
    }

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
  S = sign

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

  expand-s : s == S (n1 * d1)
  expand-s = i.isSign-unique (isSignℚ'.v v) (i.isSign-self (n1 * d1))

  end-path : s == S (n2 * d2)
  end-path = expand-s >=> i.int->sign-preserves-* >=> path >=> (sym i.int->sign-preserves-*)

  ans : isSign s (n2 * d2)
  ans = subst (\s -> isSign s (n2 * d2)) (sym end-path) (i.isSign-self (n2 * d2))

r~-preserves-NonNeg : {q1 q2 : Rational'} -> NonNeg q1 -> q1 r~ q2 -> NonNeg q2
r~-preserves-NonNeg {q1} {q2} nn-q1 r = handle (decide-sign q1)
  where
  handle : Σ[ s ∈ Sign ] isSign s q1 -> NonNeg q2
  handle (pos-sign  , p-q1) = Pos->NonNeg (r~-preserves-sign p-q1 r)
  handle (zero-sign , z-q1) = Zero->NonNeg (r~-preserves-sign z-q1 r)
  handle (neg-sign  , n-q1)  = bot-elim (NonNeg->¬Neg nn-q1 n-q1)

Zero-r~ : {q1 : Rational'} -> Zero q1 -> q1 r~ 0r'
Zero-r~ {q1} (is-signℚ' p) = *-right-one >=> p2 >=> sym (*-left-zero)
  where
  n = numer q1
  d = denom q1

  p2 : n == 0#
  p2 = i.*-right-injective (rNonZero q1) (i.Zero-path _ p >=> sym *-left-zero)

Zero-0r' : Zero 0r'
Zero-0r' = is-signℚ' (subst Zero (sym *-left-zero) tt)

Zero->Zero-numer : {q : ℚ'} -> Zero q -> Zero (numer q)
Zero->Zero-numer {q} (is-signℚ' zq) = handle (decide-sign (numer q))
  where
  handle : Σ[ s ∈ Sign ] isSign s (numer q) -> Zero (numer q)
  handle (pos-sign  , p-nq) =
    bot-elim (NonZero->¬Zero (i.*-NonZero-NonZero (inj-l p-nq) (rNonZero q)) zq)
  handle (zero-sign , z-nq) = z-nq
  handle (neg-sign  , n-nq)  =
    bot-elim (NonZero->¬Zero (i.*-NonZero-NonZero (inj-r n-nq) (rNonZero q)) zq)


private
  Pos->same-sign :
    (q : Rational') -> Pos q -> Σ[ s ∈ Sign ] (isSign s (numer q) × isSign s (denom q))
  Pos->same-sign q p = s1 , (i.isSign-self (numer q) ,
                             subst (\x -> isSign x (denom q)) (sym path) (i.isSign-self (denom q)))
    where
    s1 = sign (numer q)
    s2 = sign (denom q)
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
    (q : Rational') -> (s : Sign) -> isSign s (numer q) -> isSign s (denom q) -> Pos q
  same-sign->Pos q s@pos-sign sn sd = is-signℚ' (int.*-isSign {s} {s} {numer q} {denom q} sn sd)
  same-sign->Pos q s@neg-sign sn sd = is-signℚ' (int.*-isSign {s} {s} {numer q} {denom q} sn sd)
  same-sign->Pos q zero-sign sn sd = bot-elim (int.NonZero->¬Zero (rNonZero q) sd)

same-sign-ℤ->ℚ' : (i : ℤ) -> (s : Sign) -> isSign s i -> isSign s (ℤ->ℚ' i)
same-sign-ℤ->ℚ' i s si =
  subst (\x -> isSign x (ℤ->ℚ' i)) s*-pos-right-identity
        (is-signℚ' (int.*-isSign {s} {pos-sign} {i} {i.int 1} si tt))

Pos-ℕ⁺->ℚ' : (i : Nat⁺) -> Pos (ℕ->ℚ' ⟨ i ⟩)
Pos-ℕ⁺->ℚ' (i@(suc _) , _) = same-sign-ℤ->ℚ' (i.int i) pos-sign tt

abstract
  r+'-preserves-Pos : {q1 q2 : Rational'} -> Pos q1 -> Pos q2 -> Pos (q1 r+' q2)
  r+'-preserves-Pos {q1} {q2} p1 p2 = ans2
    where
    module _ where
      n1 = numer q1
      n2 = numer q2
      d1 = denom q1
      d2 = denom q2

    helper : (s1 s2 : Sign) -> isSign s1 n1 -> isSign s1 d1 -> isSign s2 n2 -> isSign s2 d2 ->
             Pos ((n1 * d2 + n2 * d1) * (d1 * d2))
    helper zero-sign s2        sn1 sd1 sn2 sd2 = bot-elim (NonZero->¬Zero (rNonZero q1) sd1)
    helper pos-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (NonZero->¬Zero (rNonZero q2) sd2)
    helper neg-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (NonZero->¬Zero (rNonZero q2) sd2)
    helper pos-sign  pos-sign  sn1 sd1 sn2 sd2 =
      *-Pos-Pos (+-Pos-Pos (*-Pos-Pos sn1 sd2) (*-Pos-Pos sn2 sd1)) (*-Pos-Pos sd1 sd2)
    helper pos-sign  neg-sign  sn1 sd1 sn2 sd2 =
      *-Neg-Neg (+-Neg-Neg (*-Pos-Neg sn1 sd2) (*-Neg-Pos sn2 sd1)) (*-Pos-Neg sd1 sd2)
    helper neg-sign  pos-sign  sn1 sd1 sn2 sd2 =
      *-Neg-Neg (+-Neg-Neg (*-Neg-Pos sn1 sd2) (*-Pos-Neg sn2 sd1)) (*-Neg-Pos sd1 sd2)
    helper neg-sign  neg-sign  sn1 sd1 sn2 sd2 =
      *-Pos-Pos (+-Pos-Pos (*-Neg-Neg sn1 sd2) (*-Neg-Neg sn2 sd1)) (*-Neg-Neg sd1 sd2)

    ans : Pos ((n1 * d2 + n2 * d1) * (d1 * d2))
    ans = helper s1 s2 sn1 sd1 sn2 sd2
      where
      module _ where
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
    module _ where
      n1 = numer q1
      n2 = numer q2
      d1 = denom q1
      d2 = denom q2

    helper : (s1 s2 : Sign) -> isSign s1 n1 -> isSign s1 d1 -> isSign s2 n2 -> isSign s2 d2 ->
             Pos ((n1 * n2) * (d1 * d2))
    helper zero-sign s2        sn1 sd1 sn2 sd2 = bot-elim (NonZero->¬Zero (rNonZero q1) sd1)
    helper pos-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (NonZero->¬Zero (rNonZero q2) sd2)
    helper neg-sign  zero-sign sn1 sd1 sn2 sd2 = bot-elim (NonZero->¬Zero (rNonZero q2) sd2)
    helper pos-sign  pos-sign  sn1 sd1 sn2 sd2 =
      *-Pos-Pos (*-Pos-Pos sn1 sn2) (*-Pos-Pos sd1 sd2)
    helper pos-sign  neg-sign  sn1 sd1 sn2 sd2 =
      *-Neg-Neg (*-Pos-Neg sn1 sn2) (*-Pos-Neg sd1 sd2)
    helper neg-sign  pos-sign  sn1 sd1 sn2 sd2 =
      *-Neg-Neg (*-Neg-Pos sn1 sn2) (*-Neg-Pos sd1 sd2)
    helper neg-sign  neg-sign  sn1 sd1 sn2 sd2 =
      *-Pos-Pos (*-Neg-Neg sn1 sn2) (*-Neg-Neg sd1 sd2)

    ans : Pos ((n1 * n2) * (d1 * d2))
    ans = helper s1 s2 sn1 sd1 sn2 sd2
      where
      module _ where
        full-s1 = Pos->same-sign q1 p1
        full-s2 = Pos->same-sign q2 p2
        s1 = fst full-s1
        sn1 = proj₁ (snd full-s1)
        sd1 = proj₂ (snd full-s1)
        s2 = fst full-s2
        sn2 = proj₁ (snd full-s2)
        sd2 = proj₂ (snd full-s2)

  r-'-flips-sign : (q : ℚ') (s : Sign) -> (isSign s q) -> (isSign (s⁻¹ s) (r-' q))
  r-'-flips-sign q s qs =
    is-signℚ'
      (subst (i.isSign (s⁻¹ s)) (sym i.minus-extract-left)
             (i.minus-isSign {numer q i.* denom q} {s} (isSignℚ'.v qs)))

abstract
  r+'-preserves-NonNeg : {q1 q2 : Rational'} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r+' q2)
  r+'-preserves-NonNeg {q1} {q2} (inj-r z1) nn2 = (r~-preserves-NonNeg NonNeg-0q2 0q2~q1q2)
    where
    q2~0q2 : q2 r~ (0r' r+' q2)
    q2~0q2 = subst (q2 r~_) (sym (r+'-left-zero q2)) (refl-r~ {q2})

    NonNeg-0q2 : NonNeg (0r' r+' q2)
    NonNeg-0q2 = r~-preserves-NonNeg nn2 q2~0q2

    0q2~q1q2 : (0r' r+' q2) r~ (q1 r+' q2)
    0q2~q1q2 = r+'-preserves-r~₁ q2 0r' q1 (sym (Zero-r~ z1))
  r+'-preserves-NonNeg (inj-l p1) (inj-l p2) = inj-l (r+'-preserves-Pos p1 p2)
  r+'-preserves-NonNeg {q1} {q2} (inj-l p1) (inj-r z2) = inj-l (r~-preserves-sign Pos-q10 q10~q1q2)
    where
    q1~q10 : q1 r~ (q1 r+' 0r')
    q1~q10 = subst (q1 r~_) (sym (r+'-right-zero q1)) (refl-r~ {q1})

    Pos-q10 : Pos (q1 r+' 0r')
    Pos-q10 = r~-preserves-sign p1 q1~q10

    q10~q1q2 : (q1 r+' 0r') r~ (q1 r+' q2)
    q10~q1q2 = r+'-preserves-r~₂ q1 0r' q2 (sym (Zero-r~ z2))
