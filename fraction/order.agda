{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import equality
open import fraction.sign
open import hlevel
open import rational
open import relation
open import semiring
open import sign
open import sign.instances.int
open import sign.instances.fraction
open import ring.implementations

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
