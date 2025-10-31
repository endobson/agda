{-# OPTIONS --cubical --safe --exact-split #-}

module int.sign where

open import additive-group
open import additive-group.instances.int
open import base
open import hlevel
open import int.base
open import int.order
open import nat.properties using (Pos')
open import order.instances.int
open import order
open import relation
open import sign using (Sign ; pos-sign ; zero-sign ; neg-sign ; isNonZeroSign ; isPosSign)

-- Sign based predicates

Zero : (n : Int) -> Set
Zero zero-int = Top
Zero (pos x) = Bot
Zero (neg x) = Bot

Pos : (n : Int) -> Set
Pos n = 0# < n

Neg : (n : Int) -> Set
Neg n = n < 0#

-- Switch the order on this to be more natural -- DO NOT SUBMIT
NonZero : (n : Int) -> Set
NonZero n = Pos n ⊎ Neg n

NonPos : (n : Int) -> Set
NonPos n = n ≤ 0#

NonNeg : (n : Int) -> Set
NonNeg n = 0# ≤ n

-- The sign based predicates are propositions

isPropZero : {n : Int} -> isProp (Zero n)
isPropZero {zero-int} _ _ = refl
isPropZero {pos _} ()
isPropZero {neg _} ()

isPropPos : {n : Int} -> isProp (Pos n)
isPropPos = isProp-<

isPropNeg : {n : Int} -> isProp (Neg n)
isPropNeg = isProp-<

isPropNonZero : {n : Int} -> isProp (NonZero n)
isPropNonZero = isProp⊎ isPropPos isPropNeg asym-<

isPropNonPos : {n : Int} -> isProp (NonPos n)
isPropNonPos = isProp-≤

isPropNonNeg : {n : Int} -> isProp (NonNeg n)
isPropNonNeg = isProp-≤

-- Weakening of the predicates

Pos->NonNeg : {n : Int} -> (Pos n) -> NonNeg n
Pos->NonNeg = weaken-<

Pos->NonZero : {n : Int} -> (Pos n) -> NonZero n
Pos->NonZero p = inj-l p

Neg->NonPos : {n : Int} -> (Neg n) -> NonPos n
Neg->NonPos = weaken-<

Neg->NonZero : {n : Int} -> (Neg n) -> NonZero n
Neg->NonZero n = inj-r n

Zero->NonPos : {n : Int} -> (Zero n) -> NonPos n
Zero->NonPos {zero-int} _ = refl-≤

Zero->NonNeg : {n : Int} -> (Zero n) -> NonNeg n
Zero->NonNeg {zero-int} _ = refl-≤


-- The predicates are negations of others

NonNeg->¬Neg : {n : Int} -> (NonNeg n) -> ¬(Neg n)
NonNeg->¬Neg = convert-≤

NonPos->¬Pos : {n : Int} -> (NonPos n) -> ¬(Pos n)
NonPos->¬Pos = convert-≤

NonZero->¬Zero : {n : Int} -> (NonZero n) -> ¬(Zero n)
NonZero->¬Zero {zero-int} (inj-l 0<0) _ = irrefl-< 0<0
NonZero->¬Zero {zero-int} (inj-r 0<0) _ = irrefl-< 0<0


-- Positive Nats are positive
Pos'->Pos : {n : Nat} -> (Pos' n) -> Pos (int n)
Pos'->Pos {n} p = (n , p) , +-right-zero

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
isSign-self (pos i)  = (suc i , tt) , +-right-zero
isSign-self zero-int = tt
isSign-self (neg i)  = (suc i , tt) , +-inverse

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
NonZero->NonZeroSign {m = zero-int} (inj-l 0<0) = bot-elim (irrefl-< 0<0)
NonZero->NonZeroSign {m = zero-int} (inj-r 0<0) = bot-elim (irrefl-< 0<0)
NonZero->NonZeroSign {m = neg _} _ = tt

Pos->PosSign : {m : Int} -> Pos m -> isPosSign (int->sign m)
Pos->PosSign {m = pos _} _ = tt
Pos->PosSign {m = zero-int} 0<0 = bot-elim (irrefl-< 0<0)
Pos->PosSign {m = neg i} 0<m = bot-elim (asym-< 0<m neg<0)
