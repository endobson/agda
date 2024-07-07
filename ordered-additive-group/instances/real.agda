{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.real where

open import apartness
open import additive-group
open import additive-group.instances.real
open import base
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.group
open import ordered-additive-group.negated
open import real
open import real.arithmetic.order
open import subset
open import subset.subspace
open import truncation
open import sum

instance
  LinearlyOrderedAdditiveStr-ℝ : LinearlyOrderedAdditiveStr {D = ℝ} useⁱ useⁱ
  LinearlyOrderedAdditiveStr-ℝ = LinearlyOrderedAdditiveStr-Group
    (ℝ+₁-preserves-< _ _ _)

  PartiallyOrderedAdditiveStr-ℝ : PartiallyOrderedAdditiveStr {D = ℝ} useⁱ useⁱ
  PartiallyOrderedAdditiveStr-ℝ = PartiallyOrderedAdditiveStr-Negated _ _


  opaque
    ApartAdditiveGroup-ℝ : ApartAdditiveGroup AdditiveGroup-ℝ isTightApartness-ℝ#
    ApartAdditiveGroup-ℝ = record
      { +-reflects-# = +-reflects-ℝ#
      }
      where
      +-reflects-ℝ# : {a b c d : ℝ} -> (a + b) # (c + d) -> ∥ (a # c) ⊎ (b # d) ∥
      +-reflects-ℝ# (inj-l ab<cd) = ∥-map (⊎-map inj-l inj-l) (+-reflects-< ab<cd)
      +-reflects-ℝ# (inj-r ab>cd) = ∥-map (⊎-map inj-r inj-r) (+-reflects-< ab>cd)
