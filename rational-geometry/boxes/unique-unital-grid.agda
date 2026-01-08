{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.unique-unital-grid where

open import additive-group
open import additive-group.instances.int
open import base
open import cubical
open import equality-path
open import equivalence
open import finset
open import funext
open import hlevel.base
open import hlevel.sigma
open import int
open import isomorphism
open import order
open import ordered-additive-group
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.unique-unital-box
open import rational-geometry.boxes.unital
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.point
open import rational-geometry.region
open import rational.order
open import ring.implementations.int
open import semiring
open import sigma.base
open import truncation
open import univalence


private
  module _ {ℓ : Level} (B : Boxes ℓ) (hasNoOverlap-B : hasNoOverlap B) where
    isProp-box-fiber : ∀ b -> isProp (fiber (Boxes.box B) b)
    isProp-box-fiber b (i₁ , p₁) (i₂ , p₂) =
      ΣProp-path (isSet-Box _ _)
        (hasNoOverlap-B b.bottom-left i₁ i₂
          (transport (\i -> Region.contains (Box.region (p₁ (~ i))) b.bottom-left)
                     b.bottom-left∈region)
          (transport (\i -> Region.contains (Box.region (p₂ (~ i))) b.bottom-left)
                     b.bottom-left∈region))
      where
      module b = Box b




module _
  {ℓ : Level} (B₁ B₂ : Boxes ℓ) (u : ℚ⁺)
  (isUnital-B₁ : isUnitalBoxes u B₁) (isGridAligned-B₁ : isGridAligned u B₁)
  (hasNoOverlap-B₁ : hasNoOverlap B₁)
  (isUnital-B₂ : isUnitalBoxes u B₂) (isGridAligned-B₂ : isGridAligned u B₂)
  (hasNoOverlap-B₂ : hasNoOverlap B₂)
  (region-path : Boxes.region B₁ == Boxes.region B₂)
  where

  private
    module B₁ = Boxes B₁
    module B₂ = Boxes B₂
    module R₁ = Region (Boxes.region B₁)
    module R₂ = Region (Boxes.region B₂)

    C : Type ℓ
    C = Σ[ b ∈ Box ] (fiber B₁.box b × fiber B₂.box b)

    isProp-C' : {b : Box} -> isProp (fiber B₁.box b × fiber B₂.box b)
    isProp-C' {b} = isProp× (isProp-box-fiber B₁ hasNoOverlap-B₁ b)
                            (isProp-box-fiber B₂ hasNoOverlap-B₂ b)

    C->I₁ : C -> B₁.I
    C->I₁ (_ , (i , _) , _) = i
    C->I₂ : C -> B₂.I
    C->I₂ (_ , _ , (i , _)) = i

    p->I₁ : (p : Point) (p∈R₁ : R₁.contains p) -> Σ[ i ∈ B₁.I ] (Box.contains (B₁.box i) p)
    p->I₁ p = unsquash isProp-T
      where
      isProp-T : isProp (Σ[ i ∈ B₁.I ] (Box.contains (B₁.box i) p))
      isProp-T (i₁ , c₁) (i₂ , c₂) =
        ΣProp-path (\{i} -> (snd (Region.predicate (Box.region (B₁.box i)) p)))
          (hasNoOverlap-B₁ p i₁ i₂ c₁ c₂)

    p->I₂ : (p : Point) (p∈R₂ : R₂.contains p) -> Σ[ i ∈ B₂.I ] (Box.contains (B₂.box i) p)
    p->I₂ p = unsquash isProp-T
      where
      isProp-T : isProp (Σ[ i ∈ B₂.I ] (Box.contains (B₂.box i) p))
      isProp-T (i₁ , c₁) (i₂ , c₂) =
        ΣProp-path (\{i} -> (snd (Region.predicate (Box.region (B₂.box i)) p)))
          (hasNoOverlap-B₂ p i₁ i₂ c₁ c₂)


    I₂->I₁ : (i : B₂.I) -> fiber B₁.box (B₂.box i)
    I₂->I₁ i = fst Σj , box-path
      where
      b₂ : Box
      b₂ = B₂.box i
      p : Point
      p = Box.bottom-left b₂
      p∈b₂ : Box.contains b₂ p
      p∈b₂ = Box.bottom-left∈region b₂
      Σj : Σ[ i ∈ B₁.I ] (Box.contains (B₁.box i) p)
      Σj = p->I₁ p (transport (\i -> Region.contains (region-path (~ i)) p) ∣ i , p∈b₂ ∣)
      j = fst Σj
      b₁ = B₁.box (fst Σj)
      p∈b₁ = snd Σj

      box-path : b₁ == b₂
      box-path =
        cong fst (isContr->isProp (point->∃!grid-unital-box u p)
                   (b₁ , isGridAligned-B₁ j , isUnital-B₁ j , p∈b₁)
                   (b₂ , isGridAligned-B₂ i , isUnital-B₂ i , p∈b₂))

    I₁->I₂ : (i : B₁.I) -> fiber B₂.box (B₁.box i)
    I₁->I₂ i = fst Σj , box-path
      where
      b₁ : Box
      b₁ = B₁.box i
      p : Point
      p = Box.bottom-left b₁
      p∈b₁ : Box.contains b₁ p
      p∈b₁ = Box.bottom-left∈region b₁
      Σj : Σ[ i ∈ B₂.I ] (Box.contains (B₂.box i) p)
      Σj = p->I₂ p (transport (\i -> Region.contains (region-path i) p) ∣ i , p∈b₁ ∣)
      j = fst Σj
      b₂ = B₂.box (fst Σj)
      p∈b₂ = snd Σj

      box-path : b₂ == b₁
      box-path =
        cong fst (isContr->isProp (point->∃!grid-unital-box u p)
                   (b₂ , isGridAligned-B₂ j , isUnital-B₂ j , p∈b₂)
                   (b₁ , isGridAligned-B₁ i , isUnital-B₁ i , p∈b₁))



    I₁->C : B₁.I -> C
    I₁->C i = B₁.box i , (i , refl) , (I₁->I₂ i)
    I₂->C : B₂.I -> C
    I₂->C i = B₂.box i , (I₂->I₁ i) , (i , refl)

    Iso₁ : Iso B₁.I C
    Iso₁ = iso I₁->C C->I₁ fb (\_ -> refl)
      where
      fb : ∀ x -> I₁->C (C->I₁ x) == x
      fb (_ , (_ , p) , _) = ΣProp-path isProp-C' p
    Iso₂ : Iso B₂.I C
    Iso₂ = iso I₂->C C->I₂ fb (\_ -> refl)
      where
      fb : ∀ x -> I₂->C (C->I₂ x) == x
      fb (_ , _ , (_ , p)) = ΣProp-path isProp-C' p

    I-path : B₁.I == B₂.I
    I-path i = Glue C (\{ (i = i0) -> (B₁.I , isoToEquiv Iso₁)
                        ; (i = i1) -> (B₂.I , isoToEquiv Iso₂)
                        })
    box-paths : PathP (\j -> I-path j -> Box) B₁.box B₂.box
    box-paths j i = fst (unglue (j ∨ ~ j) i)

  Boxes-unital-grid-path : B₁ == B₂
  Boxes-unital-grid-path =
    \i -> record
      { Index = index-path i
      ; box = box-paths i
      }
    where
    index-path : B₁.Index == B₂.Index
    index-path = ΣProp-path isProp-isFinSet I-path
