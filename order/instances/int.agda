{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.int where

open import base
open import int
open import int.order as io
open import order
open import truncation

instance
  LinearOrderStr-ℤ : LinearOrderStr ℤ ℓ-zero
  LinearOrderStr-ℤ = record
    { _<_ = io._<_
    ; isProp-< = \x y -> io.isProp-< {x} {y}
    ; irrefl-< = \{x} -> io.irrefl-< {x}
    ; trans-< = \{x} {y} {z} -> io.trans-< {x} {y} {z}
    ; connected-< = io.connected-<
    ; comparison-< = \i j k i<k -> ∣ io.comparison-< i<k j ∣
    }
