{-# OPTIONS --cubical --safe --exact-split #-}

module apartness.instances.rational where

open import apartness
open import apartness.discrete
open import equality
open import rational

instance
  isTightApartness-ℚ# : isTightApartness (\ (x y : ℚ) -> x != y)
  isTightApartness-ℚ# = isTightApartness-!= Discrete-ℚ
