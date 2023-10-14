{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.group where

open import base
open import category.base
open import category.instances.set
open import category.constructions.group

GroupC : (ℓ : Level) -> PreCategory (ℓ-suc ℓ) ℓ
GroupC ℓ = IGroupC (Set×-CMC ℓ)
