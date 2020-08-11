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
open import sum

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

¬fin-zero : ¬ (Fin 0)
¬fin-zero (i , p) = zero-≮ p

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
  Iso.inv suc-fin-iso' p = ΣProp-path isProp≤ (cong (fst ∘ pred-fin) p)
  Iso.rightInv suc-fin-iso' p = isSet->Square isSetFin
  Iso.leftInv  suc-fin-iso' p = isSet->Square isSetFin

-- Naturals in a range

isInRange : Nat -> Nat -> Nat -> Type₀
isInRange m n i = (m ≤ i × i < n)

isPropIsInRange : {m n i : Nat} -> isProp (isInRange m n i)
isPropIsInRange = isProp× isProp≤ isProp≤


InRange : Nat -> Nat -> Type₀
InRange m n = Σ Nat (isInRange m n)

private
  inRange->fin : {m n : Nat} -> InRange m n -> Fin (n -' m)
  inRange->fin {m} {n} (i , ((j , j+m==i) , i<n)) = j , <-minus j+'m<n
    where
    j+'m<n : (j +' m) < n
    j+'m<n = transport (\k -> j+m==i (~ k) < n) i<n

  fin->inRange : {m n : Nat} -> Fin (n -' m) -> InRange m n
  fin->inRange {m} {n} (j , j<n-m) = (j +' m , ((j , refl) , <-minus-rev j<n-m))


  fin->inRange->fin : {m n : Nat} (i : Fin (n -' m))
                      -> (inRange->fin {m} (fin->inRange i)) == i
  fin->inRange->fin _ = ΣProp-path isProp≤ refl

  inRange->fin->inRange : {m n : Nat} (i : InRange m n)
                      -> (fin->inRange (inRange->fin i)) == i
  inRange->fin->inRange (_ , ((_ , path) , _)) = ΣProp-path isPropIsInRange path

  fin-inRange-iso : {m n : Nat} -> Iso (Fin (n -' m)) (InRange m n)
  Iso.fun fin-inRange-iso = fin->inRange
  Iso.inv fin-inRange-iso = inRange->fin
  Iso.rightInv fin-inRange-iso = inRange->fin->inRange
  Iso.leftInv  (fin-inRange-iso {m} {n}) = fin->inRange->fin {m} {n}


fin-inRange-path : {m n : Nat} -> (Fin (n -' m)) == (InRange m n)
fin-inRange-path = ua (isoToEquiv fin-inRange-iso)

-- Fins based on inductive ≤

FinInd : Nat -> Type₀
FinInd n = Σ[ i ∈ Nat ] (i <i n)

zero-fin-ind : {n : Nat} -> FinInd (suc n)
zero-fin-ind = zero , zero-<i

suc-fin-ind : {n : Nat} -> FinInd n -> FinInd (suc n)
suc-fin-ind (i , p) = suc i , suc-≤i p

fin-fin-ind-iso : {n : Nat} -> Iso (Fin n) (FinInd n)
Iso.fun fin-fin-ind-iso (i , p) = (i , (Iso.fun ≤-≤i-iso p))
Iso.inv fin-fin-ind-iso (i , p) = (i , (Iso.inv ≤-≤i-iso p))
Iso.rightInv fin-fin-ind-iso (i , p) = ΣProp-path isProp≤i refl
Iso.leftInv  fin-fin-ind-iso (i , p) = ΣProp-path isProp≤ refl

Fin==FinInd : {n : Nat} -> Fin n == FinInd n
Fin==FinInd {n} k = Σ[ i ∈ Nat ] (≤==≤i {suc i} {n} k)
