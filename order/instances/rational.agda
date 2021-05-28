{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.rational where

open import base
open import order
open import rational
import rational.order as ro

instance
  LinearOrderStr-ℚ : LinearOrderStr ℚ ℓ-zero
  LinearOrderStr-ℚ = record
    { _<_ = ro._<_
    ; isProp-< = \x y -> ro.isProp-< {x} {y}
    ; irrefl-< = \{x} -> ro.irrefl-< {x}
    ; trans-< = \{x} {y} {z} -> ro.trans-< {x} {y} {z}
    ; connected-< = ro.connected-<
    ; comparison-< = ro.comparison-<
    }
