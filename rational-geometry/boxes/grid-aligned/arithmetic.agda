{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.grid-aligned.arithmetic where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import rational
open import rational-geometry.boxes.grid-aligned
open import rational.order
open import ring
open import ring.implementations.int
open import semiring

opaque
  isGridAligned-minus⁻ : (u : ℚ⁺) (q : ℚ) -> isGridAlignedℚ u (- q) -> isGridAlignedℚ u q
  isGridAligned-minus⁻ (u , 0<u) q (s , p) =
    (- s , *-left (ℤ->ℚ-preserves-minus _) >=>
           minus-extract-left >=>
           cong -_ p >=>
           minus-double-inverse)


  refine-isGridAligned : (q : ℚ) (u₁ u₂ : ℚ⁺) ->
    isGridAlignedℚ u₁ q -> isGridAlignedℚ u₂ ⟨ u₁ ⟩ ->
    isGridAlignedℚ u₂ q
  refine-isGridAligned q (u₁ , _) (u₂ , _) (n₁ , p₁) (n₂ , p₂) =
    (n₁ * n₂ , *-left (ℤ->ℚ-preserves-* _ _) >=> *-assoc >=> *-right p₂ >=> p₁)
