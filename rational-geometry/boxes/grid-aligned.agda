{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.grid-aligned where

open import apartness.instances.rational
open import base
open import equality-path
open import hlevel.base
open import hlevel.sigma
open import int.base
open import order
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.point
open import rational.integer
open import rational.order
open import semidomain
open import semidomain.instances.rational
open import semiring
open import sigma.base

isGridAlignedℚ : ℚ⁺ -> ℚ -> Type₀
isGridAlignedℚ (u , _) q = Σ[ n ∈ ℤ ] (ℤ->ℚ n * u == q)

opaque
  isProp-isGridAlignedℚ : (u : ℚ⁺) (q : ℚ) -> isProp (isGridAlignedℚ u q)
  isProp-isGridAlignedℚ (_ , 0<u) q (n₁ , p₁) (n₂ , p₂) =
    ΣProp-path (isSetℚ _ _) n₁=n₂
    where
    n₁=n₂ : n₁ == n₂
    n₁=n₂ =
      isInjective-ℤ->ℚ
        (*₂-reflects-=
          (\p -> irrefl-path-< (sym p) 0<u)
          (p₁ >=> (sym p₂)))


isGridAlignedPoint : ℚ⁺ -> Point -> Type₀
isGridAlignedPoint u (x , y) = isGridAlignedℚ u x × isGridAlignedℚ u y


isGridAligned₂Box : ℚ⁺ -> ℚ⁺ -> Box -> Type₀
isGridAligned₂Box ux uy B =
  isGridAlignedℚ ux B.left ×
  isGridAlignedℚ ux B.right ×
  isGridAlignedℚ uy B.bottom ×
  isGridAlignedℚ uy B.top
  where
  module B = Box B

isGridAlignedBox : ℚ⁺ -> Box -> Type₀
isGridAlignedBox u B = isGridAligned₂Box u u B

opaque
  isProp-isGridAlignedBox : (u : ℚ⁺) -> (B : Box) -> isProp (isGridAlignedBox u B)
  isProp-isGridAlignedBox u B =
    isProp× (isProp-isGridAlignedℚ u B.left)
     (isProp× (isProp-isGridAlignedℚ u B.right)
      (isProp× (isProp-isGridAlignedℚ u B.bottom)
               (isProp-isGridAlignedℚ u B.top)))
    where
    module B = Box B

isGridAligned₂Boxes : {ℓ : Level} -> ℚ⁺ -> ℚ⁺ -> Boxes ℓ -> Type ℓ
isGridAligned₂Boxes ux uy B =
  ∀ (i : B.I) -> isGridAligned₂Box ux uy (B.box i)
  where
  module B = Boxes B


isGridAlignedBoxes : {ℓ : Level} -> ℚ⁺ -> Boxes ℓ -> Type ℓ
isGridAlignedBoxes u B = isGridAligned₂Boxes u u B

opaque
  isProp-isGridAlignedBoxes : {ℓ : Level} -> (u : ℚ⁺) -> (B : Boxes ℓ) -> isProp (isGridAlignedBoxes u B)
  isProp-isGridAlignedBoxes u B =
    isPropΠ (\i -> isProp-isGridAlignedBox u (Boxes.box B i))
