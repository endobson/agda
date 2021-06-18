{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication4 where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.factor-order
open import rational.minmax
open import real
open import real.sequence
open import real.arithmetic.absolute-value
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation

module _ (x y : ℝ)
  where
  private
    module x = Real x
    module y = Real y
