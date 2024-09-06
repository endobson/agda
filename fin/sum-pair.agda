{-# OPTIONS --cubical --safe --exact-split #-}

module fin.sum-pair where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import hlevel
open import isomorphism
open import nat
open import nat.order

record FinPair+ (n : Nat) : Type₀ where
  constructor fin-pair+
  field
    i : Nat
    j : Nat
    i+j=n : i + j == n

FinPair+-path : {n : Nat} {p1 p2 : FinPair+ n} ->
                (FinPair+.i p1 == FinPair+.i p2) ->
                (FinPair+.j p1 == FinPair+.j p2) ->
                p1 == p2
FinPair+-path {n} {p1} {p2} q1 q2 = \i -> fin-pair+ (q1 i) (q2 i) (qp i)
  where
  opaque
    qp : PathP (\i -> q1 i + q2 i == n) (FinPair+.i+j=n p1) (FinPair+.i+j=n p2)
    qp = isProp->PathP (\i -> isSetNat (q1 i + q2 i) n)

FinPair+-path₁ : {n : Nat} {p1 p2 : FinPair+ n} ->
                 (FinPair+.i p1 == FinPair+.i p2) ->
                 p1 == p2
FinPair+-path₁ {n} {fin-pair+ p1i p1j p1p} {fin-pair+ p2i p2j p2p} q1 = FinPair+-path q1 q2
  where
  opaque
    q2 : p1j == p2j
    q2 = +'-left-injective (+-left (sym q1) >=> p1p >=> sym p2p)


FinPair+-path₂ : {n : Nat} {p1 p2 : FinPair+ n} ->
                 (FinPair+.j p1 == FinPair+.j p2) ->
                 p1 == p2
FinPair+-path₂ {n} {fin-pair+ p1i p1j p1p} {fin-pair+ p2i p2j p2p} q2 = FinPair+-path q1 q2
  where
  opaque
    q1 : p1i == p2i
    q1 = +'-right-injective (+-right (sym q2) >=> p1p >=> sym p2p)


isContr-FinPair+-0 : isContr (FinPair+ 0)
isContr-FinPair+-0 = center , same
  where
  center : FinPair+ 0
  center = (fin-pair+ zero zero refl)
  opaque
    same : (p : FinPair+ 0) -> center == p
    same (fin-pair+ i j i+j=n) =
      FinPair+-path (sym (zero-≤->zero (j , +-commuteᵉ j i >=> i+j=n)))
                    (sym (zero-≤->zero (i , i+j=n)))


FinPair+-swap : {n : Nat} -> Iso (FinPair+ n) (FinPair+ n)
FinPair+-swap .Iso.fun (fin-pair+ i j p) = (fin-pair+ j i (+-commuteᵉ j i >=> p))
FinPair+-swap .Iso.inv (fin-pair+ i j p) = (fin-pair+ j i (+-commuteᵉ j i >=> p))
FinPair+-swap .Iso.rightInv _ = FinPair+-path refl refl
FinPair+-swap .Iso.leftInv _ = FinPair+-path refl refl

fin-pair+-zero₁ : {n : Nat} -> FinPair+ n
fin-pair+-zero₁ {n} = fin-pair+ 0 n refl
fin-pair+-zero₂ : {n : Nat} -> FinPair+ n
fin-pair+-zero₂ {n} = fin-pair+ n 0 (+-commuteᵉ n 0)

fin-pair+-suc₁ : {n : Nat} -> FinPair+ n -> FinPair+ (suc n)
fin-pair+-suc₁ (fin-pair+ i j p) = fin-pair+ (suc i) j (cong suc p)
fin-pair+-suc₂ : {n : Nat} -> FinPair+ n -> FinPair+ (suc n)
fin-pair+-suc₂ (fin-pair+ i j p) = fin-pair+ i (suc j) (+'-right-suc >=> cong suc p)
