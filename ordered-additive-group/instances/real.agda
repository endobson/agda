{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.real where

open import additive-group.instances.real
open import base
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.group
open import ordered-additive-group.negated
open import real
open import real.arithmetic.order

instance
  LinearlyOrderedAdditiveStr-ℝ : LinearlyOrderedAdditiveStr {D = ℝ} useⁱ useⁱ
  LinearlyOrderedAdditiveStr-ℝ = LinearlyOrderedAdditiveStr-Group
    (ℝ+₁-preserves-< _ _ _)

  PartiallyOrderedAdditiveStr-ℝ : PartiallyOrderedAdditiveStr {D = ℝ} useⁱ useⁱ
  PartiallyOrderedAdditiveStr-ℝ = PartiallyOrderedAdditiveStr-Negated _ _
