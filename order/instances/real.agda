{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.real where

open import base
open import order
open import real

instance
  LinearOrderStr-ℝ : LinearOrderStr ℝ ℓ-one
  LinearOrderStr-ℝ = record
    { _<_ = _ℝ<_
    ; isProp-< = \{x} {y} -> isProp-ℝ< x y
    ; irrefl-< = \{x} -> irrefl-ℝ< {x}
    ; trans-< = \{x} {y} {z} -> trans-ℝ< {x} {y} {z}
    ; connected-< = \{x} {y} -> connected-ℝ< x y
    ; comparison-< = comparison-ℝ<
    }

  PartialOrderStr-ℝ : PartialOrderStr ℝ ℓ-one
  PartialOrderStr-ℝ = NegatedLinearOrder LinearOrderStr-ℝ

  CompatibleOrderStr-ℝ : CompatibleOrderStr LinearOrderStr-ℝ PartialOrderStr-ℝ
  CompatibleOrderStr-ℝ = CompatibleNegatedLinearOrder LinearOrderStr-ℝ
