{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.finset where

open import base
open import category.base
open import category.instances.set
open import category.constructions.full
open import finset

FinSetC : (ℓ : Level) -> PreCategory (ℓ-suc ℓ) ℓ
FinSetC ℓ = FullC (SetC ℓ) (\ (S , _) -> isFinSetΣ S)
