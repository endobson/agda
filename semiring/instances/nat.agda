{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.instances.nat where

open import base
open import nat
open import semiring.initial.base

open import semiring.instances.nat.base public

instance
  ℕ->SemiringStr-ℕ : ℕ->Semiring-Op ℕ
  ℕ->SemiringStr-ℕ = ℕ->SemiringStr-cons' (\n -> n) refl refl (\_ _ -> refl)
