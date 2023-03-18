{-# OPTIONS --cubical --safe --exact-split #-}

module sequence where

open import additive-group
open import additive-group.instances.nat
open import base
open import nat
open import nat.order
open import order
open import order.minmax
open import order.minmax.instances.nat
open import order.instances.nat
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

  dropN : Nat -> Seq -> Seq
  dropN n s i = s (n + i)

∀Largeℕ' : {ℓP : Level} -> Pred ℕ ℓP -> Type ℓP
∀Largeℕ' P = Σ[ n ∈ ℕ ] ((m : ℕ) -> n ≤ m -> P m)

∀Largeℕ : {ℓP : Level} -> Pred ℕ ℓP -> Type ℓP
∀Largeℕ P = ∥ ∀Largeℕ' P ∥

∀Largeℕ'-∩ : {ℓ₁ ℓ₂ : Level} {P₁ : Pred ℕ ℓ₁} {P₂ : Pred ℕ ℓ₂} ->
             ∀Largeℕ' P₁ -> ∀Largeℕ' P₂ -> ∀Largeℕ' (P₁ ∩ P₂)
∀Largeℕ'-∩ (n1 , f1) (n2 , f2) =
  n , (\ m n≤m -> f1 m (trans-≤ n1≤n n≤m) , f2 m (trans-≤ n2≤n n≤m))
  where
  n = max n1 n2
  n1≤n = max-≤-left
  n2≤n = max-≤-right

∀Largeℕ-∩ : {ℓ₁ ℓ₂ : Level} {P₁ : Pred ℕ ℓ₁} {P₂ : Pred ℕ ℓ₂} ->
             ∀Largeℕ P₁ -> ∀Largeℕ P₂ -> ∀Largeℕ (P₁ ∩ P₂)
∀Largeℕ-∩ = ∥-map2 ∀Largeℕ'-∩

∀Largeℕ'-map : {ℓ₁ ℓ₂ : Level} {P₁ : Pred ℕ ℓ₁} {P₂ : Pred ℕ ℓ₂} ->
               ({m : ℕ} -> P₁ m -> P₂ m) -> ∀Largeℕ' P₁ -> ∀Largeℕ' P₂
∀Largeℕ'-map f (n , g) = n , (\m n≤m -> f (g m n≤m))

∀Largeℕ-map : {ℓ₁ ℓ₂ : Level} {P₁ : Pred ℕ ℓ₁} {P₂ : Pred ℕ ℓ₂} ->
              ({m : ℕ} -> P₁ m -> P₂ m) -> ∀Largeℕ P₁ -> ∀Largeℕ P₂
∀Largeℕ-map f = ∥-map (∀Largeℕ'-map f)
