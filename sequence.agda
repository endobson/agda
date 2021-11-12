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

∀Largeℕ'-∩ : {ℓ₁ ℓ₂ : Level} {P₁ : Pred ℕ ℓ₁} {P₂ : Pred ℕ ℓ₂} ->
             ∀Largeℕ' P₁ -> ∀Largeℕ' P₂ -> ∀Largeℕ' (P₁ ∩ P₂)
∀Largeℕ'-∩ (n1 , f1) (n2 , f2) =
  n , (\ m m≥n -> f1 m (trans-≤ n≥n1 m≥n) , f2 m (trans-≤ n≥n2 m≥n))
  where
  n = max n1 n2
  n≥n1 = ≤-max-left
  n≥n2 = ≤-max-right

∀Largeℕ-∩ : {ℓ₁ ℓ₂ : Level} {P₁ : Pred ℕ ℓ₁} {P₂ : Pred ℕ ℓ₂} ->
             ∀Largeℕ P₁ -> ∀Largeℕ P₂ -> ∀Largeℕ (P₁ ∩ P₂)
∀Largeℕ-∩ = ∥-map2 ∀Largeℕ'-∩
