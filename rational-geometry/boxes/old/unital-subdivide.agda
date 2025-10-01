{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.old.unital-subdivide where

open import base
open import finset
open import equality-path
open import finset.instances.sigma
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.region
open import rational-geometry.boxes.old.unital-subdivide-box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.unital
open import rational.order
open import truncation

opaque
  subdivide-boxesΣ :
    {ℓ : Level} (u : ℚ⁺) (b : Boxes ℓ) -> isGridAlignedBoxes u b ->
    Σ[ B ∈ Boxes ℓ ] (isGridAlignedBoxes u B × isUnitalBoxes u B × Boxes.region B == Boxes.region b)
  subdivide-boxesΣ {ℓ} u B₀ grid = B , isGridAligned-B , isUnital-B , region-path
    where
    module B₀ = Boxes B₀

    BsΣ : (i : B₀.I) ->
      Σ[ B ∈ Boxes ℓ-zero ] (isGridAlignedBoxes u B ×
                             isUnitalBoxes u B ×
                             Boxes.region B == Box.region (B₀.box i))
    BsΣ i₀ = subdivide-boxΣ u (B₀.box i₀) (grid i₀)

    Bs : (i : B₀.I) -> Boxes ℓ-zero
    Bs i₀ = fst (BsΣ i₀)

    I : Type ℓ
    I = Σ[ i₀ ∈ B₀.I ] (Boxes.I (Bs i₀))

    isFinSet-I : isFinSet I
    isFinSet-I = isFinSet-Σ (snd B₀.Index) (\i₀ -> (snd (Boxes.Index (Bs i₀))))

    boxes : I -> Box
    boxes (i₀ , i₁) = Boxes.box (Bs i₀) i₁

    B : Boxes ℓ
    B = record
      { Index = (I , isFinSet-I)
      ; box = boxes
      }

    isGridAligned-B : isGridAlignedBoxes u B
    isGridAligned-B (i₀ , i₁)  = (fst (snd (BsΣ i₀))) i₁
    isUnital-B : isUnitalBoxes u B
    isUnital-B (i₀ , i₁)  = (fst (snd (snd (BsΣ i₀)))) i₁

    region-path : Boxes.region B == Boxes.region B₀
    region-path = region-ext (\p -> forward p , backward p)
      where
      forward : ∀ p -> Boxes.contains B p -> Boxes.contains B₀ p
      forward p = ∥-map handle
        where
        handle : Σ[ i ∈ I ] (Box.contains (boxes i) p) ->
                 Σ[ i ∈ B₀.I ] (Box.contains (B₀.box i) p)
        handle ((i₀ , i₁) , p∈b) =
          i₀ , subst (\r -> Region.contains r p) rp (∣ i₁ , p∈b ∣)
          where
          rp : Boxes.region (Bs i₀) == Box.region (B₀.box i₀)
          rp = snd (snd (snd (BsΣ i₀)))

      backward : ∀ p -> Boxes.contains B₀ p -> Boxes.contains B p
      backward p = ∥-bind handle
        where
        handle : Σ[ i ∈ B₀.I ] (Box.contains (B₀.box i) p) ->
                 ∃[ i ∈ I ] (Box.contains (boxes i) p)
        handle (i₀ , p∈b₀) =
          ∥-map (\ (i₁ , p∈b₁) -> (i₀ , i₁) , p∈b₁) p∈Bs₀
          where
          rp : Boxes.region (Bs i₀) == Box.region (B₀.box i₀)
          rp = snd (snd (snd (BsΣ i₀)))

          p∈Bs₀ : Boxes.contains (Bs i₀) p
          p∈Bs₀ = subst (\r -> Region.contains r p) (sym rp) p∈b₀
