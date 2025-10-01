{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.direction.perpendicular where

open import base
open import equivalence
open import apartness
open import apartness.instances.rational
open import additive-group
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import order.minmax.instances.rational
open import order.instances.rational
open import semiring
open import isomorphism
open import ordered-semiring
open import ordered-ring.absolute-value
open import ordered-ring
open import ordered-semiring.instances.rational
open import order
open import ring
open import relation
open import hlevel.base
open import hlevel.htype
open import sum
open import univalence
open import sigma.base
open import equality-path
open import rational
open import set-quotient
open import rational.order
open import rational-geometry.direction



module _ ((direction x₁ y₁ _) (direction x₂ y₂ _) : Direction) where
  record isPerpendicularDirection : Type ℓ-zero where
    constructor is-perpendicular-direction
    field
      path : x₁ * x₂ + y₁ * y₂ == 0#

isProp-isPerpendicularDirection : ∀ {d₁ d₂} -> isProp (isPerpendicularDirection d₁ d₂)
isProp-isPerpendicularDirection (is-perpendicular-direction p₁) (is-perpendicular-direction p₂) i =
  is-perpendicular-direction (isSetℚ _ _ p₁ p₂ i)

perpendicularˡ : Direction -> Direction
perpendicularˡ (direction x y p) =
  direction (- y) x (+-left abs-minus >=> +-commute >=> p)

perpendicularʳ : Direction -> Direction
perpendicularʳ (direction x y p) =
  direction y (- x) (+-right abs-minus >=> +-commute >=> p)


perpendicularˡʳ : ∀ d -> perpendicularˡ (perpendicularʳ d) == d
perpendicularˡʳ _ = direction-coord-path minus-double-inverse refl
perpendicularʳˡ : ∀ d -> perpendicularʳ (perpendicularˡ d) == d
perpendicularʳˡ _ = direction-coord-path refl minus-double-inverse

perpendicularˡˡ : ∀ d -> perpendicularˡ (perpendicularˡ d) == (reverse-direction d)
perpendicularˡˡ _ = direction-coord-path refl refl
perpendicularʳʳ : ∀ d -> perpendicularʳ (perpendicularʳ d) == (reverse-direction d)
perpendicularʳʳ _ = direction-coord-path refl refl


sym-isPerpendicular : ∀ {d₁ d₂} -> isPerpendicularDirection d₁ d₂ -> isPerpendicularDirection d₂ d₁
sym-isPerpendicular (is-perpendicular-direction p) =
  is-perpendicular-direction (+-cong *-commute *-commute >=> p)

isPerpendicular-perpendicularˡ : ∀ {d} -> isPerpendicularDirection d (perpendicularˡ d)
isPerpendicular-perpendicularˡ =
  is-perpendicular-direction (+-commute >=> +-right (*-commute >=> minus-extract-left) >=> +-inverse)


isPerpendicular-perpendicularʳ : ∀ {d} -> isPerpendicularDirection d (perpendicularʳ d)
isPerpendicular-perpendicularʳ =
  is-perpendicular-direction (+-right (*-commute >=> minus-extract-left) >=> +-inverse)

perpendicularˡ-preserves-isPerpendicular : ∀ {d₁ d₂} ->
  isPerpendicularDirection d₁ d₂ ->
  isPerpendicularDirection (perpendicularˡ d₁) (perpendicularˡ d₂)
perpendicularˡ-preserves-isPerpendicular (is-perpendicular-direction p) =
  is-perpendicular-direction (+-commute >=> +-right minus-extract-both >=> p)

perpendicularʳ-preserves-isPerpendicular : ∀ {d₁ d₂} ->
  isPerpendicularDirection d₁ d₂ ->
  isPerpendicularDirection (perpendicularʳ d₁) (perpendicularʳ d₂)
perpendicularʳ-preserves-isPerpendicular (is-perpendicular-direction p) =
  is-perpendicular-direction (+-commute >=> +-left minus-extract-both >=> p)

reverse-direction-preserves-isPerpendicular : ∀ {d₁ d₂} ->
  isPerpendicularDirection d₁ d₂ -> isPerpendicularDirection d₁ (reverse-direction d₂)
reverse-direction-preserves-isPerpendicular (is-perpendicular-direction p) =
  is-perpendicular-direction
    (+-cong minus-extract-right minus-extract-right >=>
     sym minus-distrib-plus >=> cong -_ p >=> minus-zero)


private
  isPerpendicularDirectionSemiDirection' : Direction -> SemiDirection -> hProp ℓ-zero
  isPerpendicularDirectionSemiDirection' d₁ =
    SetQuotientElim.rec isSet-hProp value value-path

    where
    value : Direction -> hProp ℓ-zero
    value d₂ = isPerpendicularDirection d₁ d₂ , isProp-isPerpendicularDirection

    opaque
      same-case : ∀ d₂ d₃ -> d₂ == d₃ ->
        (isPerpendicularDirection d₁ d₂) == (isPerpendicularDirection d₁ d₃)
      same-case _ _ p i = isPerpendicularDirection d₁ (p i)

      different-case : ∀ d₂ d₃ -> d₂ == reverse-direction d₃ ->
        Iso (isPerpendicularDirection d₁ d₂) (isPerpendicularDirection d₁ d₃)
      different-case d₂ d₃ p =
        isProp->iso forward backward
          isProp-isPerpendicularDirection isProp-isPerpendicularDirection

        where
        forward : isPerpendicularDirection d₁ d₂ -> isPerpendicularDirection d₁ d₃
        forward perp =
          subst (isPerpendicularDirection d₁)
            (cong reverse-direction p >=> reverse-direction-twice)
            (reverse-direction-preserves-isPerpendicular perp)

        backward : isPerpendicularDirection d₁ d₃ -> isPerpendicularDirection d₁ d₂
        backward perp =
          subst (isPerpendicularDirection d₁) (sym p) (reverse-direction-preserves-isPerpendicular perp)

      perp-path : ∀ d₂ d₃ ->
        SameSemiDirection d₂ d₃ ->
        (isPerpendicularDirection d₁ d₂) == (isPerpendicularDirection d₁ d₃)
      perp-path d₂ d₃ (inj-l p) = same-case d₂ d₃ p
      perp-path d₂ d₃ (inj-r p) = isoToPath (different-case d₂ d₃ p)

      value-path : ∀ d₂ d₃ -> SameSemiDirection d₂ d₃ -> value d₂ == value d₃
      value-path d₂ d₃ sd = ΣProp-path isProp-isProp (perp-path d₂ d₃ sd)


isPerpendicularDirectionSemiDirection : Direction -> SemiDirection -> Type₀
isPerpendicularDirectionSemiDirection d sd =
  fst (isPerpendicularDirectionSemiDirection' d sd)
isProp-isPerpendicularDirectionSemiDirection : ∀ d sd -> isProp (isPerpendicularDirectionSemiDirection d sd)
isProp-isPerpendicularDirectionSemiDirection d sd =
  snd (isPerpendicularDirectionSemiDirection' d sd)
