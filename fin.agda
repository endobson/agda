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

data Fin : Nat -> Type₀ where
 zero-fin : {n : Nat} -> Fin (suc n)
 suc-fin : {n : Nat} -> Fin n -> Fin (suc n)

fin->nat : {n : Nat} -> Fin n -> Nat
fin->nat zero-fin = zero
fin->nat (suc-fin f) = suc (fin->nat f)

zero-fin!=suc-fin : {n : Nat} {x : Fin n} -> zero-fin != (suc-fin x)
zero-fin!=suc-fin p = zero-suc-absurd (cong fin->nat p)

-- Show that Fin 0 and Fin 1 are just Bot and Top
private
  fin-zero-bot-iso : Iso (Fin 0) Bot
  Iso.fun fin-zero-bot-iso ()
  Iso.inv fin-zero-bot-iso ()
  Iso.rightInv fin-zero-bot-iso ()
  Iso.leftInv  fin-zero-bot-iso ()

  fin-one-top-iso : Iso (Fin 1) Top
  Iso.fun fin-one-top-iso zero-fin = tt
  Iso.inv fin-one-top-iso tt       = zero-fin
  Iso.rightInv fin-one-top-iso tt       = refl
  Iso.leftInv  fin-one-top-iso zero-fin = refl

fin-zero-bot-path : Fin 0 == Bot
fin-zero-bot-path = ua (isoToEquiv fin-zero-bot-iso)

fin-one-top-path : Fin 1 == Top
fin-one-top-path = ua (isoToEquiv fin-one-top-iso)

private
  pred-fin : {n : Nat} -> Fin (suc (suc n)) -> Fin (suc n)
  pred-fin zero-fin = zero-fin
  pred-fin (suc-fin x) = x

  suc-fin-injective : {n : Nat} {x y : Fin n} -> (suc-fin x) == (suc-fin y) -> x == y
  suc-fin-injective {n = (suc _)} p = (cong pred-fin p)

decide-fin : {n : Nat} (x : Fin n) -> (y : Fin n) -> Dec (x == y)
decide-fin zero-fin zero-fin = yes refl
decide-fin zero-fin (suc-fin n) = no zero-fin!=suc-fin
decide-fin (suc-fin m) zero-fin = no (zero-fin!=suc-fin ∘ sym)
decide-fin (suc-fin m) (suc-fin n) with (decide-fin m n)
...  | (yes p) = yes (cong suc-fin p)
...  | (no f) = no (\ pr -> f (suc-fin-injective pr) )

discreteFin : {n : Nat} -> Discrete (Fin n)
discreteFin = decide-fin

isSetFin : {n : Nat} -> isSet (Fin n)
isSetFin = Discrete->isSet discreteFin

private
  suc-fin-iso' : {n : Nat} {x y : Fin (suc n)} -> Iso (x == y) (suc-fin x == suc-fin y)
  Iso.fun suc-fin-iso' p = cong suc-fin p
  Iso.inv suc-fin-iso' p = suc-fin-injective p
  Iso.rightInv suc-fin-iso' p = isSet->Square isSetFin
  Iso.leftInv  suc-fin-iso' p = isSet->Square isSetFin

  suc-fin-iso : {n : Nat} {x y : Fin n} -> Iso (x == y) ((suc-fin x) == (suc-fin y))
  suc-fin-iso {n = zero}    {x} = bot-elim (transport fin-zero-bot-path x)
  suc-fin-iso {n = (suc _)}     = suc-fin-iso'

suc-fin-path : {n : Nat} {x y : Fin n} -> (x == y) == (suc-fin x == suc-fin y)
suc-fin-path = ua (isoToEquiv suc-fin-iso)

private
  fin->nat-injective : {n : Nat} {x y : Fin n} -> (fin->nat x) == (fin->nat y) -> x == y
  fin->nat-injective {_} {zero-fin} {zero-fin} _ = refl
  fin->nat-injective {_} {suc-fin x} {suc-fin y} pr =
    (transport suc-fin-path (fin->nat-injective (suc-injective pr)))
  fin->nat-injective {_} {zero-fin} {suc-fin _} pr = bot-elim (zero-suc-absurd pr)
  fin->nat-injective {_} {suc-fin _} {zero-fin} pr = bot-elim (zero-suc-absurd (sym pr))

  fin->nat-iso : {n : Nat} {x y : Fin n} -> Iso (x == y) (fin->nat x == fin->nat y)
  Iso.fun fin->nat-iso p = cong fin->nat p
  Iso.inv fin->nat-iso p = fin->nat-injective p
  Iso.rightInv fin->nat-iso _ = isSet->Square isSetNat
  Iso.leftInv  fin->nat-iso _ = isSet->Square isSetFin

fin->nat-path : {n : Nat} {x y : Fin n} -> (x == y) == (fin->nat x == fin->nat y)
fin->nat-path = ua (isoToEquiv fin->nat-iso)

-- Fin type based on ≤ instead of straight inductive structure
Fin' : Nat -> Type₀
Fin' n = Σ[ i ∈ Nat ] (i < n)

private
  fin'->fin : {n : Nat} -> Fin' n -> Fin n
  fin'->fin (zero    , (suc-≤ p)) = zero-fin
  fin'->fin ((suc i) , (suc-≤ p)) = suc-fin (fin'->fin (i , p))

  fin->fin' : {n : Nat} -> Fin n -> Fin' n
  fin->fin' zero-fin    .fst = zero
  fin->fin' zero-fin    .snd = suc-≤ zero-≤
  fin->fin' (suc-fin i) .fst = suc   (fin->fin' i .fst)
  fin->fin' (suc-fin i) .snd = suc-≤ (fin->fin' i .snd)

  fin'->fin->fin' : {n : Nat} (i : Fin' n) -> (fin->fin' (fin'->fin i)) == i
  fin'->fin->fin' (zero    , (suc-≤ zero-≤))   = refl
  fin'->fin->fin' ((suc i) , (suc-≤ p))      j = record
    { fst = suc   (fin'->fin->fin' (i , p) j .fst)
    ; snd = suc-≤ (fin'->fin->fin' (i , p) j .snd)
    }

  fin->fin'->fin : {n : Nat} (i : Fin n) -> (fin'->fin (fin->fin' i)) == i
  fin->fin'->fin zero-fin    = refl
  fin->fin'->fin (suc-fin i) = cong suc-fin (fin->fin'->fin i)

  iso-fin-fin' : {n : Nat} -> Iso (Fin n) (Fin' n)
  Iso.fun      iso-fin-fin' = fin->fin'
  Iso.inv      iso-fin-fin' = fin'->fin
  Iso.rightInv iso-fin-fin' = fin'->fin->fin'
  Iso.leftInv  iso-fin-fin' = fin->fin'->fin

Fin==Fin' : {n : Nat} -> Fin n == Fin' n
Fin==Fin' = isoToPath iso-fin-fin'
