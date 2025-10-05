{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.instances.int where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int
open import order
open import order.instances.int
open import ordered-additive-group
open import ordered-additive-group.decidable

private
   ℤ+₁-preserves-< : {a b c : ℤ} -> a < b -> (c + a) < (c + b)
   ℤ+₁-preserves-< (x , p) = x , sym +-assoc >=> +-left +-commute >=> +-assoc >=> +-right p

   ℤ+₁-preserves-≤ : {a b c : ℤ} -> a ≤ b -> (c + a) ≤ (c + b)
   ℤ+₁-preserves-≤ (x , p) = x , sym +-assoc >=> +-left +-commute >=> +-assoc >=> +-right p

opaque
  instance
    LinearlyOrderedAdditiveStr-ℤ : LinearlyOrderedAdditiveStr useⁱ useⁱ
    LinearlyOrderedAdditiveStr-ℤ =
      LinearlyOrderedAdditiveStr-Dec< ℤ+₁-preserves-<

    PartiallyOrderedAdditiveStr-ℤ : PartiallyOrderedAdditiveStr useⁱ useⁱ
    PartiallyOrderedAdditiveStr-ℤ = record
      { +₁-preserves-≤ = ℤ+₁-preserves-≤
      }
