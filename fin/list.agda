{-# OPTIONS --cubical --safe --exact-split #-}

module fin.list where

open import base
open import equality
open import fin
open import functions
open import funext
open import nat
open import nat.order.base
open import order
open import order.instances.nat
open import relation
open import truncation

private
  variable
    ℓ : Level
    A : Type ℓ

FinList : Type ℓ -> Type ℓ
FinList A = Σ[ n ∈ Nat ] (Fin n -> A)

_l∈'_ : REL A (FinList A) (levelOf A)
a l∈' (n , f) = Σ[ i ∈ Fin n ] (f i == a)

_l∈_ : REL A (FinList A) (levelOf A)
a l∈ (n , f) = ∃[ i ∈ Fin n ] (f i == a)

abstract
  element-paths->fin-list-path :
    {n1 n2 : Nat} {f1 : Fin n1 -> A} {f2 : Fin n2 -> A} ->
    n1 == n2 ->
    (∀ (i : Nat) (lt1 : i < n1) (lt2 : i < n2) -> (f1 (i , lt1) == (f2 (i , lt2)))) ->
    Path (FinList A) (n1 , f1) (n2 , f2)
  element-paths->fin-list-path {A = A} {n1} {n2} {f1} {f2} np fp =
    rec n1 n2 f1 f2 np fp
    where
    rec : (n1 n2 : Nat) (f1 : Fin n1 -> A) (f2 : Fin n2 -> A) ->
          n1 == n2 ->
          (∀ (i : Nat) (lt1 : i < n1) (lt2 : i < n2) ->
             (f1 (i , lt1)) == (f2 (i , lt2))) ->
          Path (FinList A) (n1 , f1) (n2 , f2)
    rec zero zero f1 f2 _ _ = \i -> zero , f1=f2 i
      where
      f1=f2 : f1 == f2
      f1=f2 = funExt (\j -> bot-elim (¬fin-zero j))

    rec (suc n1) (suc n2) f1 f2 np fp =
      \i -> suc (pn i), fin-rec-ans' i
      where
      fp' : (i : Nat) -> (lt1 : i < n1) -> (lt2 : i < n2) ->
            (f1 (suc-fin (i , lt1))) == (f2 (suc-fin (i , lt2)))
      fp' i lt1 lt2 = fp (suc i) _ _

      rec-ans : Path (FinList A) (n1 , (f1 ∘ suc-fin)) (n2 , (f2 ∘ suc-fin))
      rec-ans = rec n1 n2 (f1 ∘ suc-fin) (f2 ∘ suc-fin) (cong pred np) fp'

      pn : n1 == n2
      pn i = fst (rec-ans i)

      fin-rec-ans : PathP (\i -> Fin (suc (pn i)) -> A)
                          (fin-rec (f1 zero-fin) (f1 ∘ suc-fin))
                          (fin-rec (f2 zero-fin) (f2 ∘ suc-fin))
      fin-rec-ans i = fin-rec (fp zero zero-< zero-< i) (snd (rec-ans i))

      fin-rec-ans' : PathP (\i -> Fin (suc (pn i)) -> A) f1 f2
      fin-rec-ans' =
        transP-right (sym (fin-rec-reduce f1)) (transP-left fin-rec-ans (fin-rec-reduce f2))
    rec zero (suc i) f1 f2 np _ = zero-suc-absurd np
    rec (suc i) zero f1 f2 np _ = zero-suc-absurd (sym np)

  element-paths->vector-path :
    {n1 n2 : Nat} {f1 : Fin n1 -> A} {f2 : Fin n2 -> A} ->
    (np : n1 == n2) ->
    (∀ (i : Nat) (lt1 : i < n1) (lt2 : i < n2) -> (f1 (i , lt1) == (f2 (i , lt2)))) ->
    PathP (\i -> Fin (np i) -> A) f1 f2
  element-paths->vector-path {A = A} {n1} {n2} {f1} {f2} np ep =
    subst (\np -> PathP (\i -> Fin (np i) -> A) f1 f2) np'=np fp'
    where
    lp : Path (FinList A) (n1 , f1) (n2 , f2)
    lp = element-paths->fin-list-path np ep

    np' : n1 == n2
    np' i = fst (lp i)

    np'=np : np' == np
    np'=np = isSetNat _ _ _ _

    fp' : PathP (\i -> Fin (np' i) -> A) f1 f2
    fp' i = snd (lp i)
