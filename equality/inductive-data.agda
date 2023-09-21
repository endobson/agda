{-# OPTIONS --cubical --safe --exact-split #-}

module equality.inductive-data where

open import base
open import equivalence
open import isomorphism
open import equality-path

Iso-Path-Eq : {ℓ : Level} {A : Type ℓ} {a1 a2 : A} -> Iso (a1 == a2) (a1 === a2)
Iso-Path-Eq {A = A} = iso path->eq eq->path eq->path->eq path->eq->path
  where
  path->eq : {a1 a2 : A} -> (a1 == a2) -> (a1 === a2)
  path->eq {a1} {a2} p = transport (\i -> a1 === p i) refl-===

  eq->path : {a1 a2 : A} -> (a1 === a2) -> (a1 == a2)
  eq->path refl-=== = refl

  path->eq->path : {a1 a2 : A} -> (p : a1 == a2) -> eq->path (path->eq p) == p
  path->eq->path {a1} {a2} p = J (\ _ p -> eq->path (path->eq p) == p) refl-case p
    where
    refl-case : eq->path (path->eq refl) == refl
    refl-case = cong eq->path (transportRefl refl-===)

  eq->path->eq : {a1 a2 : A} -> (p : a1 === a2) -> path->eq (eq->path p) == p
  eq->path->eq refl-=== = transportRefl refl-===

Path≃Eq : {ℓ : Level} {A : Type ℓ} {a1 a2 : A} -> (a1 == a2) ≃ (a1 === a2)
Path≃Eq = isoToEquiv Iso-Path-Eq

trans-=== : {ℓ : Level} {A : Type ℓ} {a b c : A} -> (a === b) -> (b === c) -> (a === c)
trans-=== refl-=== refl-=== = refl-===
