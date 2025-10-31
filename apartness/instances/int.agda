{-# OPTIONS --cubical --safe --exact-split #-}

module apartness.instances.int where

open import apartness
open import apartness.discrete
open import equality-path
open import int.base
open import int.cover

instance
  isTightApartness-ℤ# : isTightApartness (\ (x y : ℤ) -> x != y)
  isTightApartness-ℤ# = isTightApartness-!= discreteInt
