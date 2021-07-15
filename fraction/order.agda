{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import equality
open import fraction.sign
open import hlevel
open import int.order using (trichotomous-<)
open import order
open import order.instances.int
open import rational
open import relation
open import ring.implementations
open import semiring
open import sign
open import sign.instances.int
open import sign.instances.fraction
open import truncation

import int

module fraction.order where

record _ℚ'<_ (q : ℚ') (r : ℚ') : Type₀ where
  constructor ℚ'<-cons
  field
    v : Pos (r r+' (r-' q))

_ℚ'>_ : ℚ' -> ℚ' -> Type₀
q ℚ'> r = r ℚ'< q

record _ℚ'≤_ (q : ℚ') (r : ℚ') : Type₀ where
  constructor ℚ'≤-cons
  field
    v : NonNeg (r r+' (r-' q))

_ℚ'≥_ : ℚ' -> ℚ' -> Type₀
q ℚ'≥ r = r ℚ'≤ q

isProp-ℚ'< : {q r : ℚ'} -> isProp (q ℚ'< r)
isProp-ℚ'< (ℚ'<-cons p1) (ℚ'<-cons p2) = cong ℚ'<-cons (isProp-Pos _ p1 p2)

isProp-ℚ'≤ : {q r : ℚ'} -> isProp (q ℚ'≤ r)
isProp-ℚ'≤ (ℚ'≤-cons p1) (ℚ'≤-cons p2) = cong ℚ'≤-cons (isProp-NonNeg _ p1 p2)

r~-preserves-<₁ : {q1 q2 r : Rational'} -> q1 ℚ'< r -> q1 r~ q2 -> q2 ℚ'< r
r~-preserves-<₁ {q1} {q2} {r} (ℚ'<-cons pos-diff) q1~q2 =
  ℚ'<-cons (r~-preserves-sign pos-diff
             (r+'-preserves-r~₂ r (r-' q1) (r-' q2) (r-'-preserves-r~ q1 q2 q1~q2)))

r~-preserves-<₂ : {q r1 r2 : Rational'} -> q ℚ'< r1 -> r1 r~ r2 -> q ℚ'< r2
r~-preserves-<₂ {q} {r1} {r2} (ℚ'<-cons pos-diff) r1~r2 =
  ℚ'<-cons (r~-preserves-sign pos-diff (r+'-preserves-r~₁ (r-' q) r1 r2 r1~r2))

r~-preserves-≤₁ : {q1 q2 r : Rational'} -> q1 ℚ'≤ r -> q1 r~ q2 -> q2 ℚ'≤ r
r~-preserves-≤₁ {q1} {q2} {r} (ℚ'≤-cons nn-diff) q1~q2 =
  ℚ'≤-cons (r~-preserves-NonNeg nn-diff
             (r+'-preserves-r~₂ r (r-' q1) (r-' q2) (r-'-preserves-r~ q1 q2 q1~q2)))

r~-preserves-≤₂ : {q r1 r2 : Rational'} -> q ℚ'≤ r1 -> r1 r~ r2 -> q ℚ'≤ r2
r~-preserves-≤₂ {q} {r1} {r2} (ℚ'≤-cons nn-diff) r1~r2 =
  ℚ'≤-cons (r~-preserves-NonNeg nn-diff (r+'-preserves-r~₁ (r-' q) r1 r2 r1~r2))


irrefl-ℚ'< : Irreflexive _ℚ'<_
irrefl-ℚ'< {a} (ℚ'<-cons pos-diff) = (NonPos->¬Pos (Zero->NonPos zero-diff) pos-diff)
  where
  zero-diff : Zero (a r+' (r-' a))
  zero-diff = r~-preserves-sign Zero-0r' (sym (r+'-inverse a))

trans-ℚ'< : Transitive _ℚ'<_
trans-ℚ'< {a} {b} {c} (ℚ'<-cons a<b) (ℚ'<-cons b<c) = a<c
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

  a<c : a ℚ'< c
  a<c = ℚ'<-cons (r~-preserves-sign (r+'-preserves-Pos b<c a<b) f-path)


decide-ℚ'< : Decidable2 _ℚ'<_
decide-ℚ'< x y = handle (decide-sign z')
  where
  z = y r+' (r-' x)
  z' = Rational'.numerator z * Rational'.denominator z
  handle : Σ[ s ∈ Sign ] (isSign s z') -> Dec (x ℚ'< y)
  handle (pos-sign  , pz) = yes (ℚ'<-cons (is-signℚ' pz))
  handle (zero-sign , zz) = no (\ (ℚ'<-cons pz) -> NonPos->¬Pos (Zero->NonPos zz) (isSignℚ'.v pz))
  handle (neg-sign  , nz) = no (\ (ℚ'<-cons pz) -> NonPos->¬Pos (Neg->NonPos nz) (isSignℚ'.v pz))

asym-ℚ'< : Asymmetric _ℚ'<_
asym-ℚ'< {q} {r} (ℚ'<-cons pos-d1) (ℚ'<-cons pos-d2) = NonPos->¬Pos (inj-l neg-d2) pos-d2
  where
  d1 = r r+' (r-' q)
  d2 = q r+' (r-' r)
  -d1==d2 : (r-' d1) == d2
  -d1==d2 = r-'-distrib-r+' r (r-' q) >=>
            cong ((r-' r) r+'_) (r-'-double-inverse q) >=>
            r+'-commute (r-' r) q

  neg-d2 = (subst Neg -d1==d2 (r-'-flips-sign _ pos-sign pos-d1))


private
  r~->zero-diff : {q r : ℚ'} -> (q r~ r) -> Zero (r r+' (r-' q))
  r~->zero-diff {q} {r} q~r = zd
    where
    diff = (r r+' (r-' q))
    diffᵉ = (r r+'ᵉ (r-' q))
    n = Rational'.numerator diffᵉ
    zpath : n == (int.int 0)
    zpath = +-left (sym q~r) >=>
            +-right int.minus-extract-left >=>
            int.add-minus-zero
    zn : Zero (Rational'.numerator diff)
    zn = subst Zero (sym zpath >=> cong Rational'.numerator (sym r+'-eval)) tt
    zd = is-signℚ' (int.*-Zero₁ zn)


  ℚ'<-¬r~ : {q r : ℚ'} -> q ℚ'< r -> ¬ (q r~ r)
  ℚ'<-¬r~ {q} {r} (ℚ'<-cons pos-diff) q~r = NonPos->¬Pos (inj-r (r~->zero-diff q~r)) pos-diff


trichotomous~-ℚ'< : (q r : ℚ') -> Tri (q ℚ'< r) (q r~ r) (r ℚ'< q)
trichotomous~-ℚ'< q r = handle (decide-sign d')
  where
  d = r r+' (r-' q)
  d2 = q r+' (r-' r)
  -d==d2 : (r-' d) == d2
  -d==d2 = r-'-distrib-r+' r (r-' q) >=>
           cong ((r-' r) r+'_) (r-'-double-inverse q) >=>
           r+'-commute (r-' r) q

  d' = Rational'.numerator d * Rational'.denominator d
  handle : Σ[ s ∈ Sign ] (isSign s d') -> Tri (q ℚ'< r) (q r~ r) (r ℚ'< q)
  handle (pos-sign  , pd) =
    tri< q<r (ℚ'<-¬r~ q<r) (asym-ℚ'< q<r)
    where
    q<r = (ℚ'<-cons (is-signℚ' pd))
  handle (zero-sign , zd) =
    tri= (\ (ℚ'<-cons pd) -> NonPos->¬Pos (Zero->NonPos zd) (isSignℚ'.v pd))
         (sym r~q)
         (\ (ℚ'<-cons pd2) ->
           NonZero->¬Zero (inj-l pd2)
             (subst Zero -d==d2 (r-'-flips-sign _ zero-sign (is-signℚ' zd))))
    where
    d'-path : d' == (int.int 0)
    d'-path = int.Zero-path d' zd
    n = Rational'.numerator d
    n-path : n == (int.int 0)
    n-path = int.*-left-zero-eq (Rational'.NonZero-denominator d) d'-path

    r~q : r r~ q
    r~q =
      sym int.+-right-zero >=>
      int.+-right (sym int.add-minus-zero >=>
                   int.+-commute >=>
                   +-left (sym int.minus-extract-left)) >=>
      sym int.+-assoc >=>
      int.+-left (cong Rational'.numerator (sym r+'-eval) >=> n-path) >=>
      int.+-left-zero

  handle (neg-sign  , nd) =
    tri> (\ (ℚ'<-cons pd) -> NonPos->¬Pos (Neg->NonPos nd) (isSignℚ'.v pd))
         (\ q~r -> ℚ'<-¬r~ r<q (sym q~r))
         r<q
    where
    r<q = (ℚ'<-cons (subst Pos -d==d2 (r-'-flips-sign _ neg-sign (is-signℚ' nd))))


connected~-ℚ'< : {q r : ℚ'} -> ¬(q ℚ'< r) -> ¬(r ℚ'< q) -> q r~ r
connected~-ℚ'< {q} {r} ¬q<r ¬r<q = handle (trichotomous~-ℚ'< q r)
  where

  handle : Tri (q ℚ'< r) (q r~ r) (r ℚ'< q) -> q r~ r
  handle (tri< q<r _ _) = bot-elim (¬q<r q<r)
  handle (tri= _ q~r _) = q~r
  handle (tri> _ _ r<q) = bot-elim (¬r<q r<q)

comparison-ℚ'< : Comparison _ℚ'<_
comparison-ℚ'< x y z x<z = ∣ handle (trichotomous~-ℚ'< x y) (trichotomous~-ℚ'< y z) ∣
  where
  handle : Tri (x ℚ'< y) (x r~ y) (y ℚ'< x) -> Tri (y ℚ'< z) (y r~ z) (z ℚ'< y) ->
           (x ℚ'< y) ⊎ (y ℚ'< z)
  handle (tri< x<y _ _)     _              = inj-l x<y
  handle (tri= _   _ _)     (tri< y<z _ _) = inj-r y<z
  handle (tri> _   _ _)     (tri< y<z _ _) = inj-r y<z
  handle (tri= _   x~y _)   (tri= ¬y<z _ _) = bot-elim (¬y<z (r~-preserves-<₁ x<z x~y))
  handle (tri= _   x~y _)   (tri> ¬y<z _ _) = bot-elim (¬y<z (r~-preserves-<₁ x<z x~y))
  handle (tri> _   _ y<x)   (tri= ¬y<z _ _) = bot-elim (¬y<z (trans-ℚ'< y<x x<z))
  handle (tri> _   _ y<x)   (tri> ¬y<z _ _) = bot-elim (¬y<z (trans-ℚ'< y<x x<z))