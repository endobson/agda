{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.unital-subdivide where

open import base
open import finset
open import equality-path
open import finset.instances.sigma
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.area.raw
open import rational-geometry.boxes.union-boxes
open import rational-geometry.region
open import rational-geometry.boxes.unital-subdivide-box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.unital
open import rational.order
open import finsum
open import funext
open import rational
open import truncation


opaque
  subdivide-boxesΣ :
    {ℓ : Level} (u : ℚ⁺) (B₀ : Boxes ℓ) -> isGridAligned u B₀ ->
    Σ[ B ∈ Boxes ℓ ] (
      isGridAligned u B ×
      isUnitalBoxes u B ×
      Boxes.region B == Boxes.region B₀ ×
      boxes-raw-area B == boxes-raw-area B₀ ×
      (hasNoOverlap B₀ -> hasNoOverlap B))
  subdivide-boxesΣ {ℓ} u B₀ grid =
    B , isGridAligned-B , isUnital-B , region-path , raw-area-path , hasNoOverlap-B
    where
    module B₀ = Boxes B₀

    BsΣ : (i : B₀.I) ->
      Σ[ B ∈ Boxes ℓ-zero ] (
        isGridAligned u B ×
        isUnitalBoxes u B ×
        Boxes.region B == Box.region (B₀.box i) ×
        boxes-raw-area B == Box.area (B₀.box i) ×
        hasNoOverlap B)
    BsΣ i₀ = subdivide-boxΣ u (B₀.box i₀) (grid i₀)

    Bs : (i : B₀.I) -> Boxes ℓ-zero
    Bs i₀ = fst (BsΣ i₀)

    B : Boxes ℓ
    B = union-Boxes B₀.Index Bs
    module B = Boxes B

    -- TODO move these to be about union
    isGridAligned-B : isGridAligned u B
    isGridAligned-B (i₀ , i₁)  = (fst (snd (BsΣ i₀))) i₁
    isUnital-B : isUnitalBoxes u B
    isUnital-B (i₀ , i₁)  = (fst (snd (snd (BsΣ i₀)))) i₁

    region-path : Boxes.region B == Boxes.region B₀
    region-path = region-ext (\p -> forward p , backward p)
      where
      forward : ∀ p -> Boxes.contains B p -> Boxes.contains B₀ p
      forward p = ∥-map handle
        where
        handle : Σ[ i ∈ B.I ] (Box.contains (B.box i) p) ->
                 Σ[ i ∈ B₀.I ] (Box.contains (B₀.box i) p)
        handle ((i₀ , i₁) , p∈b) =
          i₀ , subst (\r -> Region.contains r p) rp (∣ i₁ , p∈b ∣)
          where
          rp : Boxes.region (Bs i₀) == Box.region (B₀.box i₀)
          rp = fst (snd (snd (snd (BsΣ i₀))))

      backward : ∀ p -> Boxes.contains B₀ p -> Boxes.contains B p
      backward p = ∥-bind handle
        where
        handle : Σ[ i ∈ B₀.I ] (Box.contains (B₀.box i) p) ->
                 ∃[ i ∈ B.I ] (Box.contains (B.box i) p)
        handle (i₀ , p∈b₀) =
          ∥-map (\ (i₁ , p∈b₁) -> (i₀ , i₁) , p∈b₁) p∈Bs₀
          where
          rp : Boxes.region (Bs i₀) == Box.region (B₀.box i₀)
          rp = fst (snd (snd (snd (BsΣ i₀))))

          p∈Bs₀ : Boxes.contains (Bs i₀) p
          p∈Bs₀ = subst (\r -> Region.contains r p) (sym rp) p∈b₀

    hasNoOverlap-B : hasNoOverlap B₀ -> hasNoOverlap B
    hasNoOverlap-B overlap₀ =
      hasNoOverlap-union-Boxes B₀.Index Bs
        (\i -> (snd (snd (snd (snd (snd (BsΣ i)))))))
        overlap'
      where
      overlap' : NonOverlappingRegions (\i -> Boxes.region (Bs i))
      overlap' p i₁ i₂ p₁ p₂ =
        overlap₀ p i₁ i₂
          (transport (\i -> Region.contains (fst (snd (snd (snd (BsΣ i₁)))) i) p) p₁)
          (transport (\i -> Region.contains (fst (snd (snd (snd (BsΣ i₂)))) i) p) p₂)

    raw-area-path : boxes-raw-area B == boxes-raw-area B₀
    raw-area-path =
      raw-area-union-Boxes B₀.Index Bs >=>
      cong (finiteSumᵉ _) (funExt (\i -> (fst (snd (snd (snd (snd (BsΣ i))))))))
