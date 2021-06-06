{-# OPTIONS --cubical --safe --exact-split #-}

module int.sign where

open import base
open import hlevel
open import int.base
open import nat.properties using (Pos')
open import relation
open import sign

-- Sign based predicates

Zero : (n : Int) -> Set
Zero zero-int = Top
Zero (pos x) = Bot
Zero (neg x) = Bot

Pos : (n : Int) -> Set
Pos zero-int = Bot
Pos (pos x) = Top
Pos (neg x) = Bot

Neg : (n : Int) -> Set
Neg (nonneg x) = Bot
Neg (neg x) = Top

NonZero : (n : Int) -> Set
NonZero zero-int = Bot
NonZero (pos x) = Top
NonZero (neg x) = Top

NonPos : (n : Int) -> Set
NonPos zero-int = Top
NonPos (pos x) = Bot
NonPos (neg x) = Top

NonNeg : (n : Int) -> Set
NonNeg (nonneg x) = Top
NonNeg (neg x) = Bot

-- The sign based predicates are propositions

isPropZero : {n : Int} -> isProp (Zero n)
isPropZero {zero-int} _ _ = refl
isPropZero {pos _} ()
isPropZero {neg _} ()

isPropPos : {n : Int} -> isProp (Pos n)
isPropPos {zero-int} ()
isPropPos {pos _} _ _ = refl
isPropPos {neg _} ()

isPropNeg : {n : Int} -> isProp (Neg n)
isPropNeg {zero-int} ()
isPropNeg {pos _} ()
isPropNeg {neg _} _ _ = refl

isPropNonZero : {n : Int} -> isProp (NonZero n)
isPropNonZero {zero-int} ()
isPropNonZero {pos _} _ _ = refl
isPropNonZero {neg _} _ _ = refl

isPropNonPos : {n : Int} -> isProp (NonPos n)
isPropNonPos {zero-int} _ _ = refl
isPropNonPos {pos _} ()
isPropNonPos {neg _} _ _ = refl

isPropNonNeg : {n : Int} -> isProp (NonNeg n)
isPropNonNeg {zero-int} _ _ = refl
isPropNonNeg {pos _} _ _ = refl
isPropNonNeg {neg _} ()

-- Weakening of the predicates

Pos->NonNeg : {n : Int} -> .(Pos n) -> NonNeg n
Pos->NonNeg {pos n} _ = tt

Pos->NonZero : {n : Int} -> .(Pos n) -> NonZero n
Pos->NonZero {pos x} _ = tt

Neg->NonPos : {n : Int} -> .(Neg n) -> NonPos n
Neg->NonPos {neg n} _ = tt

Neg->NonZero : {n : Int} -> .(Neg n) -> NonZero n
Neg->NonZero {neg x} _ = tt

Zero->NonPos : {n : Int} -> .(Zero n) -> NonPos n
Zero->NonPos {zero-int} _ = tt

Zero->NonNeg : {n : Int} -> .(Zero n) -> NonNeg n
Zero->NonNeg {zero-int} _ = tt

-- The predicates are negations of others

NonNeg->¬Neg : {n : Int} -> .(NonNeg n) -> ¬(Neg n)
NonNeg->¬Neg {nonneg _} _ ()
NonNeg->¬Neg {neg _} ()

NonPos->¬Pos : {n : Int} -> .(NonPos n) -> ¬(Pos n)
NonPos->¬Pos {zero-int} _ ()
NonPos->¬Pos {neg _} _ ()
NonPos->¬Pos {pos _} ()

NonZero->¬Zero : {n : Int} -> .(NonZero n) -> ¬(Zero n)
NonZero->¬Zero {zero-int} ()
NonZero->¬Zero {neg _} _ ()
NonZero->¬Zero {pos _} _ ()


-- Positive Nats are positive
Pos'->Pos : {n : Nat} -> .(Pos' n) -> Pos (int n)
Pos'->Pos {suc _} _ = tt

-- Zero ints are zero
Zero-path : (n : Int) -> Zero n -> n == (int 0)
Zero-path zero-int _ = refl


-- Sign based propositions

int->sign : Int -> Sign
int->sign (pos x)  = pos-sign
int->sign zero-int = zero-sign
int->sign (neg x)  = neg-sign

isSign : Sign -> Pred Int ℓ-zero
isSign pos-sign  = Pos
isSign zero-sign = Zero
isSign neg-sign  = Neg

isProp-isSign : (s : Sign) -> {i : Int} -> isProp (isSign s i)
isProp-isSign pos-sign = isPropPos
isProp-isSign zero-sign = isPropZero
isProp-isSign neg-sign = isPropNeg

isSign-self : (x : Int) -> isSign (int->sign x) x
isSign-self (pos _)  = tt
isSign-self zero-int = tt
isSign-self (neg _)  = tt

isSign-unique : {x : Int} {s1 s2 : Sign} -> isSign s1 x -> isSign s2 x -> s1 == s2
isSign-unique {_} {pos-sign}  {pos-sign}  p1 p2 = refl
isSign-unique {_} {pos-sign}  {zero-sign} p1 p2 = bot-elim (NonPos->¬Pos (Zero->NonPos p2) p1)
isSign-unique {_} {pos-sign}  {neg-sign}  p1 p2 = bot-elim (NonPos->¬Pos (Neg->NonPos p2) p1)
isSign-unique {_} {zero-sign} {pos-sign}  p1 p2 = bot-elim (NonPos->¬Pos (Zero->NonPos p1) p2)
isSign-unique {_} {zero-sign} {zero-sign} p1 p2 = refl
isSign-unique {_} {zero-sign} {neg-sign}  p1 p2 = bot-elim (NonNeg->¬Neg (Zero->NonNeg p1) p2)
isSign-unique {_} {neg-sign}  {pos-sign}  p1 p2 = bot-elim (NonNeg->¬Neg (Pos->NonNeg p2) p1)
isSign-unique {_} {neg-sign}  {zero-sign} p1 p2 = bot-elim (NonNeg->¬Neg (Zero->NonNeg p2) p1)
isSign-unique {_} {neg-sign}  {neg-sign}  p1 p2 = refl

NonZero->NonZeroSign : {m : Int} -> NonZero m -> isNonZeroSign (int->sign m)
NonZero->NonZeroSign {m = pos _} _ = tt
NonZero->NonZeroSign {m = neg _} _ = tt

Pos->PosSign : {m : Int} -> Pos m -> isPosSign (int->sign m)
Pos->PosSign {m = pos _} _ = tt

SignStr-Int : SignStr Int ℓ-zero
SignStr-Int = record
  { isSign = isSign
  ; isProp-isSign = \s x -> isProp-isSign s {x}
  ; isSign-unique = \x s1 s2 -> isSign-unique {x} {s1} {s2}
  }
