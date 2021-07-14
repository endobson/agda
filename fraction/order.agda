{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import equality
open import fraction.sign
open import hlevel
open import rational
open import sign
open import sign.instances.fraction

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

isProp-ℚ<' : {q r : ℚ'} -> isProp (q ℚ'< r)
isProp-ℚ<' (ℚ'<-cons p1) (ℚ'<-cons p2) = cong ℚ'<-cons (isProp-Pos _ p1 p2)

isProp-ℚ≤' : {q r : ℚ'} -> isProp (q ℚ'≤ r)
isProp-ℚ≤' (ℚ'≤-cons p1) (ℚ'≤-cons p2) = cong ℚ'≤-cons (isProp-NonNeg _ p1 p2)
