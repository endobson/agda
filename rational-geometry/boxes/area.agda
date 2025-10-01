{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.area where

open import base
open import equality-path
open import equivalence
open import hlevel.base
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.decide-unital-grid-overlap
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.area.raw
open import rational-geometry.boxes.remove-overlap
open import rational-geometry.boxes.grid-scale-exists
open import rational-geometry.boxes.area.subdivision-independent
open import rational-geometry.boxes.unital
open import rational-geometry.boxes.unital-subdivide
open import rational-geometry.region
open import rational.order
open import truncation


private
  canonical-subdivisionΣ' : {ℓ : Level} ->
    (B₀ : Boxes ℓ) ->
    Σ[ u ∈ ℚ⁺ ] Σ[ B ∈ Boxes ℓ ] (
      isGridAlignedBoxes u B ×
      isUnitalBoxes u B ×
      hasNoOverlap B ×
      Boxes.region B == Boxes.region B₀ ×
      (hasNoOverlap B₀ -> boxes-raw-area B == boxes-raw-area B₀))
  canonical-subdivisionΣ' {ℓ} B₀ =
    (u , B₂ , isGridAligned₂ , isUnital₂ , hasNoOverlap₂ ,
     region-path₂ >=> region-path₁ ,
     same-raw-area-hasNoOverlap)
    where
    Σscale : Σ[ u ∈ ℚ⁺ ] (isGridAlignedBoxes u B₀)
    Σscale = Boxes->Σscale B₀

    u : ℚ⁺
    u = fst Σscale

    Σsplit-boxes : Σ[ B ∈ Boxes ℓ ]
      (isGridAlignedBoxes u B ×
       isUnitalBoxes u B ×
       Boxes.region B == Boxes.region B₀ ×
       boxes-raw-area B == boxes-raw-area B₀ ×
       (hasNoOverlap B₀ -> hasNoOverlap B))
    Σsplit-boxes = subdivide-boxesΣ u B₀ (snd Σscale)

    B₁ : Boxes ℓ
    B₁ = fst Σsplit-boxes

    isGridAligned₁ : isGridAlignedBoxes u B₁
    isGridAligned₁ = fst (snd Σsplit-boxes)

    isUnital₁ : isUnitalBoxes u B₁
    isUnital₁ = fst (snd (snd Σsplit-boxes))

    region-path₁ : Boxes.region B₁ == Boxes.region B₀
    region-path₁ = fst (snd (snd (snd Σsplit-boxes)))

    raw-area-path₁ : boxes-raw-area B₁ == boxes-raw-area B₀
    raw-area-path₁ = fst (snd (snd (snd (snd Σsplit-boxes))))

    hasNoOverlap₁ : hasNoOverlap B₀ -> hasNoOverlap B₁
    hasNoOverlap₁ = snd (snd (snd (snd (snd Σsplit-boxes))))

    Σunique-boxes : Σ[ B ∈ Boxes ℓ ]
      (hasNoOverlap B ×
       (∀ (i : Boxes.I B) -> ∥ fiber (Boxes.box B₁) (Boxes.box B i) ∥) ×
       Boxes.region B == Boxes.region ⟨ Σsplit-boxes ⟩ ×
       (hasNoOverlap B₁ -> (B == B₁)))
    Σunique-boxes =
      remove-overlaps/decidable B₁
        (decide-unital-grid-overlap u (fst Σsplit-boxes) (fst (snd Σsplit-boxes)) (fst (snd (snd Σsplit-boxes))))

    B₂ : Boxes ℓ
    B₂ = fst Σunique-boxes

    hasNoOverlap₂ : hasNoOverlap B₂
    hasNoOverlap₂ = fst (snd Σunique-boxes)

    fibers₂ : ∀ (i : Boxes.I B₂) -> ∥ fiber (Boxes.box B₁) (Boxes.box B₂ i) ∥
    fibers₂ = fst (snd (snd Σunique-boxes))

    region-path₂ : Boxes.region B₂ == Boxes.region B₁
    region-path₂ = fst (snd (snd (snd Σunique-boxes)))

    isGridAligned₂ : isGridAlignedBoxes u B₂
    isGridAligned₂ i =
      unsquash (isProp-isGridAlignedBox u (Boxes.box B₂ i))
        (∥-map (\ (i₁ , p) -> subst (isGridAlignedBox u) p (isGridAligned₁ i₁))
          (fibers₂ i))

    isUnital₂ : isUnitalBoxes u B₂
    isUnital₂ i =
      unsquash (isProp-isUnitalBox u (Boxes.box B₂ i))
        (∥-map (\ (i₁ , p) -> subst (isUnitalBox u) p (isUnital₁ i₁))
          (fibers₂ i))

    same-raw-area-hasNoOverlap : hasNoOverlap B₀ -> boxes-raw-area B₂ == boxes-raw-area B₀
    same-raw-area-hasNoOverlap overlap₀ =
      cong boxes-raw-area (snd (snd (snd (snd Σunique-boxes))) (hasNoOverlap₁ overlap₀)) >=>
      raw-area-path₁

  canonical-subdivisionΣ : {ℓ : Level} ->
    (B₀ : Boxes ℓ) ->
    Σ[ u ∈ ℚ⁺ ] Σ[ B ∈ Boxes ℓ ] (
      isGridAlignedBoxes u B ×
      isUnitalBoxes u B ×
      hasNoOverlap B ×
      Boxes.region B == Boxes.region B₀)
  canonical-subdivisionΣ B₀ using
    (u , B , g , unital , o , rp , _) <- canonical-subdivisionΣ' B₀ =
    (u , B , g , unital , o , rp)


  subdivisionΣ->area : {ℓ : Level} ->
    (R : Region ℓ) ->
    Σ[ u ∈ ℚ⁺ ] Σ[ B ∈ Boxes ℓ ] (
      isGridAlignedBoxes u B ×
      isUnitalBoxes u B ×
      hasNoOverlap B ×
      Boxes.region B == R) ->
    ℚ
  subdivisionΣ->area _ (_ , B , _) = boxes-raw-area B

  subdivision∃->area : {ℓ : Level} ->
    (R : Region ℓ) ->
    ∃[ u ∈ ℚ⁺ ] Σ[ B ∈ Boxes ℓ ] (
      isGridAlignedBoxes u B ×
      isUnitalBoxes u B ×
      hasNoOverlap B ×
      Boxes.region B == R) ->
    ℚ
  subdivision∃->area R =
    ∥->Set isSetℚ (subdivisionΣ->area R) same
    where
    same : ∀ sub₁ sub₂ -> subdivisionΣ->area R sub₁ == subdivisionΣ->area R sub₂
    same (u₁ , B₁ , g₁ , un₁ , o₁ , rp₁) (u₂ , B₂ , g₂ , un₂ , o₂ , rp₂) =
      isSubdivisionIndependent-raw-area u₁ u₂
        (B₁ , g₁ , un₁ , o₁) (B₂ , g₂ , un₂ , o₂) (rp₁ >=> sym rp₂)

opaque
  boxes-area : {ℓ : Level} -> Boxes ℓ -> ℚ
  boxes-area B₀ = subdivision∃->area (Boxes.region B₀) (∣ canonical-subdivisionΣ B₀ ∣)

  boxes-area-hasNoOverlap :
    {ℓ : Level} -> (B : Boxes ℓ) ->
    hasNoOverlap B -> boxes-area B == boxes-raw-area B
  boxes-area-hasNoOverlap B overlaps =
    snd (snd (snd (snd (snd (snd (canonical-subdivisionΣ' B)))))) overlaps

  boxes-area-same-region :
    {ℓ : Level} -> (B₁ : Boxes ℓ) (B₂ : Boxes ℓ) ->
    (Boxes.region B₁ == Boxes.region B₂) ->
    boxes-area B₁ == boxes-area B₂
  boxes-area-same-region {ℓ} B₁ B₂ rp =
    \i -> subdivision∃->area (rp i) (sub-path i)
    where
    sub-path :
      PathP (\i ->
        ∃[ u ∈ ℚ⁺ ] Σ[ B ∈ Boxes ℓ ] (
          isGridAlignedBoxes u B ×
          isUnitalBoxes u B ×
          hasNoOverlap B ×
          Boxes.region B == (rp i)))
        (∣ canonical-subdivisionΣ B₁ ∣)
        (∣ canonical-subdivisionΣ B₂ ∣)
    sub-path = isProp->PathP (\_ -> squash)
