{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module order.instances.fin where

open import base
open import fin
open import functions
open import hlevel.base
open import nat
open import order
open import order.instances.nat
open import relation
open import sum
open import truncation

data Fin< {n : Nat} (i j : Fin n) : Type ℓ-zero where
  fin< : (Fin.i i) < (Fin.i j) -> Fin< i j

fin<⁻ : {n : Nat} {i j : Fin n} -> Fin< i j -> Fin.i i < Fin.i j
fin<⁻ (fin< lt) = lt

private
  isProp-Fin< : {n : Nat} {i j : Fin n} -> isProp (Fin< i j)
  isProp-Fin< (fin< lt1) (fin< lt2) i = fin< (isProp-< lt1 lt2 i)

  irrefl-Fin< : {n : Nat} -> Irreflexive (Fin< {n})
  irrefl-Fin< (fin< lt) = irrefl-< lt

  trans-Fin< : {n : Nat} -> Transitive (Fin< {n})
  trans-Fin< (fin< lt1) (fin< lt2) = fin< (trans-< lt1 lt2)

  connected-Fin< : {n : Nat} -> Connected (Fin< {n})
  connected-Fin< ¬lt1 ¬lt2 =
    fin-i-path (connected-< (¬lt1 ∘ fin<) (¬lt2 ∘ fin<))

  comparison-Fin< : {n : Nat} -> Comparison (Fin< {n})
  comparison-Fin< a b c (fin< a<c) =
    ∥-map (⊎-map fin< fin<) (comparison-< (Fin.i a) (Fin.i b) (Fin.i c) a<c)

instance
  isLinearOrder-Fin< : {n : Nat} -> isLinearOrder (Fin< {n})
  isLinearOrder-Fin< = record
    { isProp-< = isProp-Fin<
    ; irrefl-< = irrefl-Fin<
    ; trans-< = trans-Fin<
    ; connected-< = connected-Fin<
    ; comparison-< = comparison-Fin<
    }

private
  trichotomous-Fin< : {n : Nat} -> Trichotomous (Fin< {n})
  trichotomous-Fin< i j = handle (trichotomous-< i' j')
    where
    i' = Fin.i i
    j' = Fin.i j
    handle : Tri< i' j' -> Tri< i j
    handle (tri< lt _ _) = tri<' (fin< lt)
    handle (tri= _ eq _) = tri=' (fin-i-path eq)
    handle (tri> _ _ gt) = tri>' (fin< gt)

instance
  DecidableLinearOrderStr-Fin :
    {n : Nat} -> DecidableLinearOrderStr (isLinearOrder-Fin< {n})
  DecidableLinearOrderStr-Fin = record
    { trichotomous-< = trichotomous-Fin<
    }

data Fin≤ {n : Nat} (i j : Fin n) : Type ℓ-zero where
  fin≤ : (Fin.i i) ≤ (Fin.i j) -> Fin≤ i j

fin≤⁻ : {n : Nat} {i j : Fin n} -> Fin≤ i j -> Fin.i i ≤ Fin.i j
fin≤⁻ (fin≤ le) = le

private
  isProp-Fin≤ : {n : Nat} {i j : Fin n} -> isProp (Fin≤ i j)
  isProp-Fin≤ (fin≤ le1) (fin≤ le2) i = fin≤ (isProp-≤ le1 le2 i)

  refl-Fin≤ : {n : Nat} -> Reflexive (Fin≤ {n})
  refl-Fin≤ = fin≤ refl-≤

  trans-Fin≤ : {n : Nat} -> Transitive (Fin≤ {n})
  trans-Fin≤ (fin≤ le1) (fin≤ le2) = fin≤ (trans-≤ le1 le2)

  antisym-Fin≤ : {n : Nat} -> Antisymmetric (Fin≤ {n})
  antisym-Fin≤ (fin≤ le1) (fin≤ le2) = fin-i-path (antisym-≤ le1 le2)

instance
  isPartialOrder-Fin≤ : {n : Nat} -> isPartialOrder (Fin≤ {n})
  isPartialOrder-Fin≤ = record
    { isProp-≤ = isProp-Fin≤
    ; refl-≤ = refl-Fin≤
    ; trans-≤ = trans-Fin≤
    ; antisym-≤ = antisym-Fin≤
    }
