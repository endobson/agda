{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.triangle.base where

open import base
open import equality-path
open import rational-geometry.point
open import rational-geometry.line
open import rational-geometry.line-segment

record areNonColinear (p₁ p₂ p₃ : Point) : Type ℓ-zero where
  field
    p₁!=p₂ : p₁ != p₂
    p₂!=p₃ : p₂ != p₃
    p₃!=p₁ : p₃ != p₁

    ¬p₃∈p₁p₂ : ¬ (OnLine p₃ (line-segment->line (line-segment p₁ p₂ p₁!=p₂)))

record Triangle : Type ℓ-zero where
  field
    p₁ p₂ p₃ : Point
    non-colinear : areNonColinear p₁ p₂ p₃
