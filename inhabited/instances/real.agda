{-# OPTIONS --cubical --safe --exact-split #-}

module inhabited.instances.real where

open import additive-group
open import additive-group.instances.real
open import inhabited
open import real
open import truncation

instance
  InhabitedStr-ℝ : InhabitedStr ℝ
  InhabitedStr-ℝ = record { elem = ∣ 0# ∣ }
