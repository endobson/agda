{-# OPTIONS --cubical --safe --exact-split #-}

module heyting-field.instances.real where

open import equality
open import funext
open import heyting-field
open import order.instances.real
open import real.apartness
open import ring.implementations.real
open import univalence

instance
  ℝField : Field ℝRing isTightApartness-ℝ#
  ℝField = record
    { f#-path = (sym (funExt2 (\x y -> (ua (ℝ#≃diff# x y)))))
    }
