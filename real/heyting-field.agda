{-# OPTIONS --cubical --safe --exact-split #-}

module real.heyting-field where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import funext
open import heyting-field
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import real
open import real.apartness
open import ring.implementations.real
open import sum
open import truncation
open import univalence

instance
  ℝField : Field ℝRing isTightApartness-ℝ#
  ℝField = record
    { f#-path = (sym (funExt2 (\x y -> (ua (ℝ#≃diff# x y)))))
    }

  abstract
    ApartAdditiveGroup-ℝ : ApartAdditiveGroup AdditiveGroup-ℝ isTightApartness-ℝ#
    ApartAdditiveGroup-ℝ = record
      { +-reflects-# = +-reflects-ℝ#
      }
      where
      +-reflects-ℝ# : {a b c d : ℝ} -> (a + b) # (c + d) -> ∥ (a # c) ⊎ (b # d) ∥
      +-reflects-ℝ# (inj-l ab<cd) = ∥-map (⊎-map inj-l inj-l) (+-reflects-< ab<cd)
      +-reflects-ℝ# (inj-r ab>cd) = ∥-map (⊎-map inj-r inj-r) (+-reflects-< ab>cd)
