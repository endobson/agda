{-# OPTIONS --cubical --safe --exact-split #-}

module int.sign where

open import base
open import hlevel
open import int.base
open import nat.properties using (Pos')

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

-- The predicates are negations of others

NonNeg->¬Neg : {n : Int} -> .(NonNeg n) -> ¬(Neg n)
NonNeg->¬Neg {nonneg _} _ ()
NonNeg->¬Neg {neg _} ()

NonPos->¬Pos : {n : Int} -> .(NonPos n) -> ¬(Pos n)
NonPos->¬Pos {zero-int} _ ()
NonPos->¬Pos {neg _} _ ()
NonPos->¬Pos {pos _} ()

-- Positive Nats are positive
Pos'->Pos : {n : Nat} -> .(Pos' n) -> Pos (int n)
Pos'->Pos {suc _} _ = tt
