{-# OPTIONS --cubical --safe --exact-split #-}

module nat.bounded where

open import base
open import nat.order
open import relation

private
  variable
    ℓ : Level
    P Q : Pred Nat ℓ

-- Bounded predicates
isBounded : {ℓ : Level} -> (Pred Nat ℓ) -> Type ℓ
isBounded P = Σ[ n ∈ Nat ] (P ⊆ (_< n))

isBounded-∩₁ : isBounded P -> isBounded (P ∩ Q)
isBounded-∩₁ (n , f) = (n , (\(p , _) -> f p))

isBounded-∩₂ : isBounded Q -> isBounded (P ∩ Q)
isBounded-∩₂ (n , f) = (n , (\(_ , q) -> f q))
