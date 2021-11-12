{-# OPTIONS --cubical --safe --exact-split #-}

module sequence where

open import base
open import nat
open import relation
open import truncation

private
  variable
    ℓ : Level

Sequence : Type ℓ -> Type ℓ
Sequence D = ℕ -> D

module _ {D : Type ℓ} where
  private
    Seq : Type ℓ
    Seq = Sequence D

  constant-seq : D -> Seq
  constant-seq x _ = x

  seq-cons : D -> Seq -> Seq
  seq-cons x s zero    = x
  seq-cons x s (suc n) = s n

  drop1 : Seq -> Seq
  drop1 s n = s (suc n)

∀Largeℕ' : {ℓP : Level} -> Pred ℕ ℓP -> Type ℓP
∀Largeℕ' P = Σ[ n ∈ ℕ ] ((m : ℕ) -> n ≤ m -> P m)

∀Largeℕ : {ℓP : Level} -> Pred ℕ ℓP -> Type ℓP
∀Largeℕ P = ∥ ∀Largeℕ' P ∥