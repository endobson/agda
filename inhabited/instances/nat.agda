{-# OPTIONS --cubical --safe --exact-split #-}

module inhabited.instances.nat where

open import base
open import inhabited
open import truncation

instance
  InhabitedStr-Nat : InhabitedStr Nat
  InhabitedStr-Nat = record { elem = ∣ zero ∣ }
