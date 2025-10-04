{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.real where

open import apartness
open import additive-group
open import additive-group.apartness
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
    ApartAdditiveCommMonoid-ℝ : ApartAdditiveCommMonoid AdditiveCommMonoid-ℝ isTightApartness-ℝ#
    ApartAdditiveCommMonoid-ℝ = record
      { StronglyInjective-+₁ = \_ -> +₁-preserves-ℝ#
      ; StronglyExtensional-+₁ = \_ -> +₁-reflects-ℝ#
      }
      where
      +₁-preserves-ℝ# : {a b c : ℝ} -> b # c -> (a + b) # (a + c)
      +₁-preserves-ℝ# (inj-l b<c) = inj-l (+₁-preserves-< b<c)
      +₁-preserves-ℝ# (inj-r b>c) = inj-r (+₁-preserves-< b>c)

      +₁-reflects-ℝ# : {a b c : ℝ} -> (a + b) # (a + c) -> b # c
      +₁-reflects-ℝ# (inj-l ab<ac) = inj-l (+₁-reflects-< ab<ac)
      +₁-reflects-ℝ# (inj-r ab>ac) = inj-r (+₁-reflects-< ab>ac)
