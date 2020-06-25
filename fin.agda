{-# OPTIONS --cubical --safe --exact-split #-}

module fin where

open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import nat
open import relation
open import sigma

-- Fin type is based on ≤ instead of straight inductive structure
-- This is so that things compute better when using transport.

Fin : Nat -> Type₀
Fin n = Σ[ i ∈ Nat ] (i < n)

zero-fin : {n : Nat} -> Fin (suc n)
zero-fin = 0 , zero-<

suc-fin : {n : Nat} -> Fin n -> Fin (suc n)
suc-fin (i , p) = suc i , suc-≤ p

zero-fin!=suc-fin : {n : Nat} {x : Fin n} -> zero-fin != (suc-fin x)
zero-fin!=suc-fin p = zero-suc-absurd (cong fst p)

-- Show that Fin 0 and Fin 1 are just Bot and Top
private
  fin-zero-bot-iso : Iso (Fin 0) Bot
  Iso.fun fin-zero-bot-iso (_ , p) = zero-≮ p
  Iso.inv fin-zero-bot-iso ()
  Iso.rightInv fin-zero-bot-iso ()
  Iso.leftInv  fin-zero-bot-iso (_ , p) = bot-elim (zero-≮ p)

  fin-one-top-iso : Iso (Fin 1) Top
  Iso.fun fin-one-top-iso _ = tt
  Iso.inv fin-one-top-iso _ = zero-fin
  Iso.rightInv fin-one-top-iso tt                       = refl
  Iso.leftInv  fin-one-top-iso (zero  , suc-≤ (zero-≤)) = refl
  Iso.leftInv  fin-one-top-iso (suc i , lt)             = bot-elim (zero-≮ (pred-≤ lt))

fin-zero-bot-path : Fin 0 == Bot
fin-zero-bot-path = ua (isoToEquiv fin-zero-bot-iso)

fin-one-top-path : Fin 1 == Top
fin-one-top-path = ua (isoToEquiv fin-one-top-iso)

-- Fin is a Set

decide-fin : {n : Nat} (x : Fin n) -> (y : Fin n) -> Dec (x == y)
decide-fin (i , p1) (j , p2) with decide-nat i j
... | (no i≠j)  = no (i≠j ∘ cong fst)
... | (yes i==j) = yes (ΣProp-path isProp≤ i==j)

discreteFin : {n : Nat} -> Discrete (Fin n)
discreteFin = decide-fin

isSetFin : {n : Nat} -> isSet (Fin n)
isSetFin = Discrete->isSet discreteFin

fin->nat : {n : Nat} -> Fin n -> Nat
fin->nat (i , p) = i

private
  fin->nat-iso : {n : Nat} {x y : Fin n} -> Iso (x == y) (fin->nat x == fin->nat y)
  Iso.fun fin->nat-iso = cong fin->nat
  Iso.inv fin->nat-iso = ΣProp-path isProp≤
  Iso.rightInv fin->nat-iso _ = isSet->Square isSetNat
  Iso.leftInv  fin->nat-iso _ = isSet->Square isSetFin

fin->nat-path : {n : Nat} {x y : Fin n} -> (x == y) == (fin->nat x == fin->nat y)
fin->nat-path = ua (isoToEquiv fin->nat-iso)

private
  pred-fin : {n : Nat} -> Fin (suc (suc n)) -> Fin (suc n)
  pred-fin (zero  , p)  = (zero , zero-<)
  pred-fin (suc i , p)  = (i    , pred-≤ p)

  suc-fin-iso' : {n : Nat} {x y : Fin (suc n)} -> Iso (x == y) (suc-fin x == suc-fin y)
  Iso.fun suc-fin-iso' p = cong suc-fin p
  Iso.inv suc-fin-iso' p = cong pred-fin p
  Iso.rightInv suc-fin-iso' p = isSet->Square isSetFin
  Iso.leftInv  suc-fin-iso' p = isSet->Square isSetFin

  suc-fin-iso : {n : Nat} {x y : Fin n} -> Iso (x == y) ((suc-fin x) == (suc-fin y))
  suc-fin-iso {n = zero}    {x} = bot-elim (transport fin-zero-bot-path x)
  suc-fin-iso {n = (suc _)}     = suc-fin-iso'

  suc-fin-path : {n : Nat} {x y : Fin n} -> (x == y) == (suc-fin x == suc-fin y)
  suc-fin-path = ua (isoToEquiv suc-fin-iso)
