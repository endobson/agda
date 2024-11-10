{-# OPTIONS --cubical --safe --exact-split #-}

module subfinite.discrete where

open import subfinite

open import base
open import relation
open import finset
open import discrete
open import truncation

private
  variable
    ℓ : Level
    A B : Type ℓ

isBFinSet->Discrete : isBFinSet A ℓ -> Discrete A
isBFinSet->Discrete {A = A} {ℓ = ℓ} bfs = unsquash isProp-Discrete (∥-map handle bfs)
  where
  handle : isBFinSetΣ A ℓ -> Discrete A
  handle ((B , fsB) , (f , inj)) = isInjective->Discrete f inj (isFinSet->Discrete fsB)
