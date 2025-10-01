{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.unital where

open import additive-group
open import base
open import hlevel.base
open import hlevel.sigma
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational.order

isUnitalBox : ℚ⁺ -> Box -> Type₀
isUnitalBox (u , _) B =
  diff B.left B.right == u ×
  diff B.bottom B.top == u
  where
  module B = Box B

isProp-isUnitalBox : (u : ℚ⁺) -> (b : Box) -> isProp (isUnitalBox u b)
isProp-isUnitalBox u b = isProp× (isSetℚ _ _) (isSetℚ _ _)

isUnitalBoxes : {ℓ : Level} -> ℚ⁺ -> Boxes ℓ -> Type ℓ
isUnitalBoxes u B =
  ∀ (i : B.I) -> isUnitalBox u (B.box i)
  where
  module B = Boxes B

isProp-isUnitalBoxes : {ℓ : Level} -> (u : ℚ⁺) -> (b : Boxes ℓ) -> isProp (isUnitalBoxes u b)
isProp-isUnitalBoxes u b = isPropΠ (\i -> isProp-isUnitalBox u (Boxes.box b i))
