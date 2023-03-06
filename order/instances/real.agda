{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.real where

open import apartness
open import base
open import equivalence
open import order
open import real
open import real.order

instance
  LinearOrderStr-ℝ : LinearOrderStr ℝ ℓ-one
  LinearOrderStr-ℝ = record
    { _<_ = _ℝ<_
    ; isLinearOrder-< = record
      { isProp-< = \{x} {y} -> isProp-ℝ< x y
      ; irrefl-< = \{x} -> irrefl-ℝ< {x}
      ; trans-< = \{x} {y} {z} -> trans-ℝ< {x} {y} {z}
      ; connected-< = \{x} {y} -> connected-ℝ< x y
      ; comparison-< = comparison-ℝ<
      }
    }

  PartialOrderStr-ℝ : PartialOrderStr ℝ ℓ-one
  PartialOrderStr-ℝ = NegatedLinearOrder LinearOrderStr-ℝ

  CompatibleOrderStr-ℝ : CompatibleOrderStr LinearOrderStr-ℝ PartialOrderStr-ℝ
  CompatibleOrderStr-ℝ = CompatibleNegatedLinearOrder LinearOrderStr-ℝ

  TightApartnessStr-ℝ : TightApartnessStr ℝ ℓ-one
  TightApartnessStr-ℝ = LinearOrderTightApartnessStr LinearOrderStr-ℝ

  ApartLinearOrderStr-ℝ : ApartLinearOrderStr TightApartnessStr-ℝ LinearOrderStr-ℝ
  ApartLinearOrderStr-ℝ = record
    { <>-equiv-# = idEquiv _
    }
