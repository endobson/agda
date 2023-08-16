{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.real where

open import apartness
open import base
open import equivalence
open import order
open import real
open import real.order

instance
  isLinearOrder-ℝ< : isLinearOrder _ℝ<_
  isLinearOrder-ℝ< = record
    { isProp-< = \{x} {y} -> isProp-ℝ< x y
    ; irrefl-< = \{x} -> irrefl-ℝ< {x}
    ; trans-< = \{x} {y} {z} -> trans-ℝ< {x} {y} {z}
    ; connected-< = \{x} {y} -> connected-ℝ< x y
    ; comparison-< = comparison-ℝ<
    }

  isPartialOrder-ℝ≤ : isPartialOrder (\x y -> ¬ (y ℝ< x))
  isPartialOrder-ℝ≤ = isLinearOrder->isPartialOrder-≯ isLinearOrder-ℝ<

  CompatibleOrderStr-ℝ : CompatibleOrderStr useⁱ useⁱ
  CompatibleOrderStr-ℝ = CompatibleNegatedLinearOrder isLinearOrder-ℝ<

  isTightApartness-ℝ# : isTightApartness (\ (x y : ℝ) -> x <> y)
  isTightApartness-ℝ# = isLinearOrder->isTightApartness-<> isLinearOrder-ℝ<

  ApartLinearOrderStr-ℝ : ApartLinearOrderStr useⁱ useⁱ
  ApartLinearOrderStr-ℝ = record
    { <>-equiv-# = idEquiv _
    }
