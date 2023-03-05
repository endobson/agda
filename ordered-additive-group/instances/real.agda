{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.real where

open import additive-group.instances.real
open import base
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.group
open import ordered-additive-group.negated
open import real.arithmetic.order

instance
  LinearlyOrderedAdditiveStr-ℝ : LinearlyOrderedAdditiveStr useⁱ LinearOrderStr-ℝ
  LinearlyOrderedAdditiveStr-ℝ = LinearlyOrderedAdditiveStr-Group
    (ℝ+₁-preserves-< _ _ _)

  PartiallyOrderedAdditiveStr-ℝ : PartiallyOrderedAdditiveStr useⁱ PartialOrderStr-ℝ
  PartiallyOrderedAdditiveStr-ℝ = PartiallyOrderedAdditiveStr-Negated _ _
