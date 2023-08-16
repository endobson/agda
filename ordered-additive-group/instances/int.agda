{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.int where

open import base
open import additive-group.instances.int
open import ordered-additive-group
open import ordered-additive-group.decidable
open import order.instances.int

import int.order as io

abstract
  instance
    LinearlyOrderedAdditiveStr-ℤ : LinearlyOrderedAdditiveStr useⁱ useⁱ
    LinearlyOrderedAdditiveStr-ℤ =
      LinearlyOrderedAdditiveStr-Dec< (io.+₁-preserves-< _)

    PartiallyOrderedAdditiveStr-ℤ : PartiallyOrderedAdditiveStr useⁱ useⁱ
    PartiallyOrderedAdditiveStr-ℤ = record
      { +₁-preserves-≤ = io.+₁-preserves-≤ _
      }
