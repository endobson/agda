{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.rational where

open import base
open import ordered-additive-group
open import ordered-additive-group.decidable
open import rational

open import rational.order public using
  ( LinearlyOrderedAdditiveStr-ℚ
  ; PartiallyOrderedAdditiveStr-ℚ
  )

instance
  StronglyPartiallyOrderedAdditiveStr-ℚ :
    StronglyPartiallyOrderedAdditiveStr useⁱ useⁱ
  StronglyPartiallyOrderedAdditiveStr-ℚ = StronglyPartiallyOrderedAdditiveStr-Dec<
