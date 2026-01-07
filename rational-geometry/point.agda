{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.point where

open import base
open import equality-path
open import hlevel.base
open import rational

record Point : Type₀ where
  constructor _,_
  field
    x : ℚ
    y : ℚ

opaque
  isSet-Point : isSet Point
  isSet-Point (x₁ , y₁) (x₂ , y₂) p₁ p₂ i j =
    isSetℚ x₁ x₂ (cong Point.x p₁) (cong Point.x p₂) i j ,
    isSetℚ y₁ y₂ (cong Point.y p₁) (cong Point.y p₂) i j
