{-# OPTIONS --cubical --safe --exact-split #-}

module fin.sum-pair where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import fin
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

fin-pair+-rec₁ : {ℓA : Level} {A : Type ℓA} {n : Nat} -> A -> (FinPair+ n -> A) -> FinPair+ (suc n) -> A
fin-pair+-rec₁ z s (fin-pair+ zero _ _) = z
fin-pair+-rec₁ z s (fin-pair+ (suc i) j p) = s (fin-pair+ i j (cong pred p))

fin-pair+-rec₂ : {ℓA : Level} {A : Type ℓA} {n : Nat} -> A -> (FinPair+ n -> A) -> FinPair+ (suc n) -> A
fin-pair+-rec₂ z s (fin-pair+ _ zero _) = z
fin-pair+-rec₂ z s (fin-pair+ i (suc j) p) = s (fin-pair+ i j (cong pred (sym +'-right-suc >=> p)))

fin-pair+-rec₁-zero :
  {ℓA : Level} {A : Type ℓA} {n : Nat} {z : A} {s : (FinPair+ n -> A)} ->
  fin-pair+-rec₁ z s fin-pair+-zero₁ == z
fin-pair+-rec₁-zero = refl

fin-pair+-rec₂-zero :
  {ℓA : Level} {A : Type ℓA} {n : Nat} {z : A} {s : (FinPair+ n -> A)} ->
  fin-pair+-rec₂ z s fin-pair+-zero₂ == z
fin-pair+-rec₂-zero = refl

fin-pair+-rec₁-suc :
  {ℓA : Level} {A : Type ℓA} {n : Nat} (z : A) (s : (FinPair+ n -> A)) (x : FinPair+ n) ->
  fin-pair+-rec₁ z s (fin-pair+-suc₁ x) == s x
fin-pair+-rec₁-suc z s x = cong s (FinPair+-path refl refl)

fin-pair+-rec₂-suc :
  {ℓA : Level} {A : Type ℓA} {n : Nat} (z : A) (s : (FinPair+ n -> A)) (x : FinPair+ n) ->
  fin-pair+-rec₂ z s (fin-pair+-suc₂ x) == s x
fin-pair+-rec₂-suc z s x = cong s (FinPair+-path refl refl)

FinPair+-Fin-Iso : {n : Nat} -> Iso (FinPair+ n) (Fin (suc n))
FinPair+-Fin-Iso {n} .Iso.fun (fin-pair+ i j p) = (i , j , +-commuteᵉ j (suc i) >=> cong suc p)
FinPair+-Fin-Iso {n} .Iso.inv (i , j , p) = (fin-pair+ i j (cong pred (+-commuteᵉ (suc i) j >=> p)))
FinPair+-Fin-Iso {n} .Iso.rightInv (i , j , p) = fin-i-path refl
FinPair+-Fin-Iso {n} .Iso.leftInv (fin-pair+ i j p) = FinPair+-path refl refl
