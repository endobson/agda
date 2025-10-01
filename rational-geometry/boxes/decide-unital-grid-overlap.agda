{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.decide-unital-grid-overlap where

open import base
open import decision
open import discrete
open import equality-path
open import hlevel.base
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.discrete
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.unique-unital-box
open import rational-geometry.boxes.unital
open import rational-geometry.point
open import rational.order

module _ {ℓ : Level}
  (u : ℚ⁺) (B : Boxes ℓ)
  (isGrid-B : isGridAlignedBoxes u B)
  (isUnital-B : isUnitalBoxes u B)
  where

  opaque
    decide-unital-grid-overlap : ∀ i₁ i₂ ->
      (Boxes.box B i₁ == Boxes.box B i₂) ⊎
      (∀ p -> Box.contains (Boxes.box B i₁) p -> Box.contains (Boxes.box B i₂) p -> Bot)
    decide-unital-grid-overlap i₁ i₂ =
      dec-case inj-l (\ ¬path -> inj-r (\p p∈b₁ p∈b₂ -> ¬path (convert p p∈b₁ p∈b₂)))
        (decide-= (Boxes.box B i₁) (Boxes.box B i₂))
      where
      convert :
        (p : Point) ->
        (Box.contains (Boxes.box B i₁) p) ->
        (Box.contains (Boxes.box B i₂) p) ->
        (Boxes.box B i₁) == (Boxes.box B i₂)
      convert p p∈b₁ p∈b₂ =
        cong fst (isContr->isProp (point->∃!grid-unital-box u p)
          (Boxes.box B i₁ , isGrid-B i₁ , isUnital-B i₁ , p∈b₁)
          (Boxes.box B i₂ , isGrid-B i₂ , isUnital-B i₂ , p∈b₂))
