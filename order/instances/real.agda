{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.real where

open import base
open import order
open import real

instance
  LinearOrderStr-ℝ : LinearOrderStr ℝ ℓ-zero
  LinearOrderStr-ℝ = record
    { _<_ = _ℝ<_
    ; isProp-< = \x y -> isProp-ℝ< x y
    ; irrefl-< = \{x} -> irrefl-ℝ< {x}
    ; trans-< = \{x} {y} {z} -> trans-ℝ< {x} {y} {z}
    ; connected-< = \{x} {y} -> connected-ℝ< x y
    ; comparison-< = comparison-ℝ<
    }
