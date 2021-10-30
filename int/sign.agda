{-# OPTIONS --cubical --safe --exact-split #-}

module int.sign where

open import base
open import hlevel
open import int.base
open import nat.properties using (Pos')
open import relation
open import sign using (Sign ; pos-sign ; zero-sign ; neg-sign ; isNonZeroSign ; isPosSign)

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
NonZero n = Pos n ⊎ Neg n

NonPos : (n : Int) -> Set
NonPos n = Neg n ⊎ Zero n

NonNeg : (n : Int) -> Set
NonNeg n = Pos n ⊎ Zero n

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
isPropNonZero {zero-int} (inj-l ())
isPropNonZero {zero-int} (inj-r ())
isPropNonZero {pos _} (inj-l _) (inj-l _) = refl
isPropNonZero {neg _} (inj-r _) (inj-r _) = refl

isPropNonPos : {n : Int} -> isProp (NonPos n)
isPropNonPos {pos _} (inj-l ())
isPropNonPos {pos _} (inj-r ())
isPropNonPos {neg _} (inj-l _) (inj-l _) = refl
isPropNonPos {zero-int} (inj-r _) (inj-r _) = refl

isPropNonNeg : {n : Int} -> isProp (NonNeg n)
isPropNonNeg {neg _} (inj-l ())
isPropNonNeg {neg _} (inj-r ())
isPropNonNeg {pos _} (inj-l _) (inj-l _) = refl
isPropNonNeg {zero-int} (inj-r _) (inj-r _) = refl

-- Weakening of the predicates

Pos->NonNeg : {n : Int} -> .(Pos n) -> NonNeg n
Pos->NonNeg {pos n} _ = inj-l tt

Pos->NonZero : {n : Int} -> .(Pos n) -> NonZero n
Pos->NonZero {pos x} _ = inj-l tt

Neg->NonPos : {n : Int} -> .(Neg n) -> NonPos n
Neg->NonPos {neg n} _ = inj-l tt

Neg->NonZero : {n : Int} -> .(Neg n) -> NonZero n
Neg->NonZero {neg x} _ = inj-r tt

Zero->NonPos : {n : Int} -> .(Zero n) -> NonPos n
Zero->NonPos {zero-int} _ = inj-r tt

Zero->NonNeg : {n : Int} -> .(Zero n) -> NonNeg n
Zero->NonNeg {zero-int} _ = inj-r tt

-- The predicates are negations of others

NonNeg->¬Neg : {n : Int} -> (NonNeg n) -> ¬(Neg n)
NonNeg->¬Neg {nonneg _} _ ()
NonNeg->¬Neg {neg _} (inj-l ())
NonNeg->¬Neg {neg _} (inj-r ())

NonPos->¬Pos : {n : Int} -> (NonPos n) -> ¬(Pos n)
NonPos->¬Pos {zero-int} _ ()
NonPos->¬Pos {neg _} _ ()
NonPos->¬Pos {pos _} (inj-l ())
NonPos->¬Pos {pos _} (inj-r ())

NonZero->¬Zero : {n : Int} -> (NonZero n) -> ¬(Zero n)
NonZero->¬Zero {zero-int} (inj-l ())
NonZero->¬Zero {zero-int} (inj-r ())
NonZero->¬Zero {neg _} _ ()
NonZero->¬Zero {pos _} _ ()


-- Positive Nats are positive
Pos'->Pos : {n : Nat} -> .(Pos' n) -> Pos (int n)
Pos'->Pos {suc _} _ = tt

-- All Nats are non-negative
NonNeg-nonneg : (n : Nat) -> NonNeg (nonneg n)
NonNeg-nonneg zero = inj-r tt
NonNeg-nonneg (suc _) = inj-l tt

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
NonZero->NonZeroSign {m = zero-int} (inj-l ())
NonZero->NonZeroSign {m = zero-int} (inj-r ())
NonZero->NonZeroSign {m = neg _} _ = tt

Pos->PosSign : {m : Int} -> Pos m -> isPosSign (int->sign m)
Pos->PosSign {m = pos _} _ = tt
