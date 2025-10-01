{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.area.subdivision-independent where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import fin
open import finite-commutative-monoid.sigma
open import finset
open import finset.instances.sigma
open import finsum
open import funext
open import int
open import int.base
open import int.sign
open import nat
open import order
open import order.instances.fin
open import order.instances.int
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.natural-reciprocal
open import rational
open import rational-geometry.boxes.area.raw
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.grid-scale-exists
open import rational-geometry.boxes.subdivide-box
open import rational-geometry.boxes.union-boxes
open import rational-geometry.boxes.unique-unital-grid
open import rational-geometry.boxes.unital
open import rational-geometry.point
open import rational-geometry.region
open import rational.order
open import ring.implementations.rational
open import semiring
open import semiring.natural-reciprocal
open import sigma.base
open import truncation

subdivide-Boxes : {ℓ : Level} -> Boxes ℓ -> Nat⁺ -> Nat⁺ -> Boxes ℓ
subdivide-Boxes Bs nx ny =
  union-Boxes (Boxes.Index Bs) (\i -> subdivide-Box (Boxes.box Bs i) nx ny)

subdivide-Boxes-preserves-region : {ℓ : Level} -> (B : Boxes ℓ) -> (nx ny : Nat⁺) ->
  Boxes.region (subdivide-Boxes B nx ny) == Boxes.region B
subdivide-Boxes-preserves-region {ℓ} B nx ny = region-ext (\p -> ∥-map (for p) , ∥-bind (back p))
  where
  B' : Boxes ℓ
  B' = subdivide-Boxes B nx ny
  module B = Boxes B
  module B' = Boxes B'

  for : (p : Point) -> Σ[ i ∈ B'.I ] (Box.contains (B'.box i) p) -> Σ[ i ∈ B.I ] (Box.contains (B.box i) p)
  for p ((i₁ , i₂) , p∈b) = i₁ , subst (\r -> Region.contains r p) rp p∈b'
    where
    b' : Boxes ℓ-zero
    b' = subdivide-Box (B.box i₁) nx ny

    p∈b' : Region.contains (Boxes.region b') p
    p∈b' = ∣ i₂ , p∈b ∣

    rp : Boxes.region b' == Box.region (B.box i₁)
    rp = subdivide-Box-same-Region (B.box i₁) nx ny

  back : (p : Point) -> Σ[ i ∈ B.I ] (Box.contains (B.box i) p) -> ∃[ i ∈ B'.I ] (Box.contains (B'.box i) p)
  back p (i , p∈b) = ∥-map (\ (i₂ , p∈b'') -> (i , i₂) , p∈b'') p∈b'
    where
    b' : Boxes ℓ-zero
    b' = subdivide-Box (B.box i) nx ny

    rp : Boxes.region b' == Box.region (B.box i)
    rp = subdivide-Box-same-Region (B.box i) nx ny

    p∈b' : Region.contains (Boxes.region b') p
    p∈b' = subst (\r -> Region.contains r p) (sym rp) p∈b


subdivide-Boxes-preserves-raw-area : {ℓ : Level} -> (B : Boxes ℓ) -> (nx ny : Nat⁺) ->
  boxes-raw-area (subdivide-Boxes B nx ny) == boxes-raw-area B
subdivide-Boxes-preserves-raw-area B nx ny =
  raw-area-union-Boxes (Boxes.Index B) (\i -> subdivide-Box (Boxes.box B i) nx ny) >=>
  cong (finiteSumᵉ (Boxes.Index B)) (funExt (\i ->
    subdivide-Box-same-raw-area (Boxes.box B i) nx ny))

subdivide-Box-hasNoOverlap : (b : Box) (nx ny : Nat⁺) -> hasNoOverlap (subdivide-Box b nx ny)
subdivide-Box-hasNoOverlap b nx ny p i₁ i₂ p∈b₁ p∈b₂ =
  \k -> x-path i₁ i₂ p∈b₁ p∈b₂ k , y-path i₁ i₂ p∈b₁ p∈b₂ k
  where
  B : Boxes ℓ-zero
  B = subdivide-Box b nx ny
  module B = Boxes B

  x-step₁ :
    ∀ (i₁@(ix₁ , _)  i₂@(ix₂ , _) : B.I) ->
    Box.contains (B.box i₁) p -> Box.contains (B.box i₂) p ->
    ¬ (ix₁ < ix₂)
  x-step₁ i₁@((ix₁ , _) , _) i₂@((ix₂ , _) , _) (_ , px<b₁r , _ , _) (b₂l≤px , _ , _) (fin< ix₁<ix₂) =
    convert-≤ le lt
    where
    lt : Box.left (B.box i₂) < Box.right (B.box i₁)
    lt = trans-≤-< b₂l≤px px<b₁r

    le : Box.right (B.box i₁) ≤ Box.left (B.box i₂)
    le =
      +₁-preserves-≤
        (*₂-preserves-≤
          (ℕ->ℚ-preserves-≤ ix₁<ix₂)
          (*-preserves-0≤
            (diff-0≤⁺ (weaken-< (Box.left<right b)))
            (0≤1/ℕ nx)))

  x-path :
    ∀ (i₁@(ix₁ , _)  i₂@(ix₂ , _) : B.I) ->
    Box.contains (B.box i₁) p -> Box.contains (B.box i₂) p -> ix₁ == ix₂
  x-path i₁ i₂ p∈b₁ p∈b₂ = connected-< (x-step₁ i₁ i₂ p∈b₁ p∈b₂) (x-step₁ i₂ i₁ p∈b₂ p∈b₁)


  y-step₁ :
    ∀ (i₁@(_ , iy₁)  i₂@(_ , iy₂) : B.I) ->
    Box.contains (B.box i₁) p -> Box.contains (B.box i₂) p ->
    ¬ (iy₁ < iy₂)
  y-step₁ i₁@(_ , (iy₁ , _)) i₂@(_ , (iy₂ , _)) (_ , _ , _ , py<b₁t) (_ , _ , b₂b≤py , _) (fin< iy₁<iy₂) =
    convert-≤ le lt
    where
    lt : Box.bottom (B.box i₂) < Box.top (B.box i₁)
    lt = trans-≤-< b₂b≤py py<b₁t

    le : Box.top (B.box i₁) ≤ Box.bottom (B.box i₂)
    le =
      +₁-preserves-≤
        (*₂-preserves-≤
          (ℕ->ℚ-preserves-≤ iy₁<iy₂)
          (*-preserves-0≤
            (diff-0≤⁺ (weaken-< (Box.bottom<top b)))
            (0≤1/ℕ ny)))

  y-path :
    ∀ (i₁@(_ , iy₁)  i₂@(_ , iy₂) : B.I) ->
    Box.contains (B.box i₁) p -> Box.contains (B.box i₂) p -> iy₁ == iy₂
  y-path i₁ i₂ p∈b₁ p∈b₂ = connected-< (y-step₁ i₁ i₂ p∈b₁ p∈b₂) (y-step₁ i₂ i₁ p∈b₂ p∈b₁)




subdivide-Boxes-preserves-hasNoOverlap : {ℓ : Level} -> (B : Boxes ℓ) -> (nx ny : Nat⁺) ->
  hasNoOverlap B -> hasNoOverlap (subdivide-Boxes B nx ny)
subdivide-Boxes-preserves-hasNoOverlap B nx ny no-overlap p (i₁ , j₁) (i₂ , j₂) p∈b₁ p∈b₂ =
  \k -> i₁=i₂ k , j₁=j₂ k
  where
  p∈b₁' : Box.contains (Boxes.box B i₁) p
  p∈b₁' =
    subst (\r -> Region.contains r p)
          (subdivide-Box-same-Region (Boxes.box B i₁) nx ny)
          (∣ j₁ , p∈b₁ ∣)

  p∈b₂' : Box.contains (Boxes.box B i₂) p
  p∈b₂' =
    subst (\r -> Region.contains r p)
          (subdivide-Box-same-Region (Boxes.box B i₂) nx ny)
          (∣ j₂ , p∈b₂ ∣)


  i₁=i₂ : i₁ == i₂
  i₁=i₂ = no-overlap p i₁ i₂ p∈b₁' p∈b₂'


  p∈b₂'' : Box.contains (Boxes.box (subdivide-Box (Boxes.box B i₂) nx ny) j₁) p
  p∈b₂'' =
    subst (\i -> Box.contains (Boxes.box (subdivide-Box (Boxes.box B i) nx ny) j₁) p) i₁=i₂
          p∈b₁

  j₁=j₂ : j₁ == j₂
  j₁=j₂ = subdivide-Box-hasNoOverlap (Boxes.box B i₂) nx ny p j₁ j₂ p∈b₂'' p∈b₂









module _ {ℓ : Level}
  (u₁ u₂ : ℚ⁺)
  ((B₁ , g₁ , unital₁ , o₁) : Σ[ B ∈ Boxes ℓ ] (isGridAlignedBoxes u₁ B × isUnitalBoxes u₁ B × hasNoOverlap B))
  ((B₂ , g₂ , unital₂ , o₂) : Σ[ B ∈ Boxes ℓ ] (isGridAlignedBoxes u₂ B × isUnitalBoxes u₂ B × hasNoOverlap B))
  (region-path : Boxes.region B₁ == Boxes.region B₂)
  where


  private
    Σu₃ : Σ[ u ∈ ℚ⁺ ] (isGridAlignedℚ u ⟨ u₁ ⟩ × isGridAlignedℚ u ⟨ u₂ ⟩)
    Σu₃ = ℚ²->Σscale ⟨ u₁ ⟩ ⟨ u₂ ⟩

    u₃ : ℚ⁺
    u₃ = fst Σu₃

    n₁ℤ : ℤ
    n₁ℤ = (fst (fst (snd Σu₃)))
    n₁ℤ-path : ℤ->ℚ n₁ℤ * ⟨ u₃ ⟩ == ⟨ u₁ ⟩
    n₁ℤ-path = (snd (fst (snd Σu₃)))
    0<n₁ℤ : 0# < n₁ℤ
    0<n₁ℤ = ℤ->ℚ-reflects-< _ _ (*₂-reflects-0< (trans-<-= (snd u₁) (sym n₁ℤ-path)) (asym-< (snd u₃)))

    n₁ : Nat⁺
    n₁ = abs' n₁ℤ , Pos'-abs' (inj-l 0<n₁ℤ)
    n₁-path : (u₁ /ℕ n₁) == u₃
    n₁-path = ΣProp-path isProp-<
      (*-left (sym n₁ℤ-path) >=> *-commute >=> sym *-assoc >=>
       *-left (*-right (cong ℤ->ℚ (nonneg-abs' (weaken-< 0<n₁ℤ))) >=> 1/ℕ-ℕ-path n₁) >=>
       *-left-one)

    n₂ℤ : ℤ
    n₂ℤ = (fst (snd (snd Σu₃)))
    n₂ℤ-path : ℤ->ℚ n₂ℤ * ⟨ u₃ ⟩ == ⟨ u₂ ⟩
    n₂ℤ-path = (snd (snd (snd Σu₃)))
    0<n₂ℤ : 0# < n₂ℤ
    0<n₂ℤ = ℤ->ℚ-reflects-< _ _ (*₂-reflects-0< (trans-<-= (snd u₂) (sym n₂ℤ-path)) (asym-< (snd u₃)))

    n₂ : Nat⁺
    n₂ = abs' n₂ℤ , Pos'-abs' (inj-l 0<n₂ℤ)
    n₂-path : (u₂ /ℕ n₂) == u₃
    n₂-path = ΣProp-path isProp-<
      (*-left (sym n₂ℤ-path) >=> *-commute >=> sym *-assoc >=>
       *-left (*-right (cong ℤ->ℚ (nonneg-abs' (weaken-< 0<n₂ℤ))) >=> 1/ℕ-ℕ-path n₂) >=>
       *-left-one)



    B₁' : Boxes ℓ
    B₁' = subdivide-Boxes B₁ n₁ n₁

    g₁' : isGridAlignedBoxes u₃ B₁'
    g₁' =
      subst (\u -> isGridAlignedBoxes u B₁') n₁-path
        (\ (i₁ , i₂) -> subdivide-Box-isGridAligned (Boxes.box B₁ i₁) n₁ u₁ (g₁ i₁) i₂)

    unital₁' : isUnitalBoxes u₃ B₁'
    unital₁' =
      subst (\u -> isUnitalBoxes u B₁') n₁-path
        (\ (i₁ , i₂) -> subdivide-Box-isUnital (Boxes.box B₁ i₁) n₁ u₁ (unital₁ i₁) i₂)

    o₁' : hasNoOverlap B₁'
    o₁' = subdivide-Boxes-preserves-hasNoOverlap B₁ n₁ n₁ o₁

    B₂' : Boxes ℓ
    B₂' = subdivide-Boxes B₂ n₂ n₂

    g₂' : isGridAlignedBoxes u₃ B₂'
    g₂' =
      subst (\u -> isGridAlignedBoxes u B₂') n₂-path
        (\ (i₁ , i₂) -> subdivide-Box-isGridAligned (Boxes.box B₂ i₁) n₂ u₂ (g₂ i₁) i₂)

    unital₂' : isUnitalBoxes u₃ B₂'
    unital₂' =
      subst (\u -> isUnitalBoxes u B₂') n₂-path
        (\ (i₁ , i₂) -> subdivide-Box-isUnital (Boxes.box B₂ i₁) n₂ u₂ (unital₂ i₁) i₂)

    o₂' : hasNoOverlap B₂'
    o₂' = subdivide-Boxes-preserves-hasNoOverlap B₂ n₂ n₂ o₂


    B₁'=B₂' : B₁' == B₂'
    B₁'=B₂' = Boxes-unital-grid-path B₁' B₂' u₃ unital₁' g₁' o₁' unital₂' g₂' o₂'
      (subdivide-Boxes-preserves-region B₁ n₁ n₁ >=>
       region-path >=>
       sym (subdivide-Boxes-preserves-region B₂ n₂ n₂))

  opaque
    isSubdivisionIndependent-raw-area : boxes-raw-area B₁ == boxes-raw-area B₂
    isSubdivisionIndependent-raw-area =
      sym (subdivide-Boxes-preserves-raw-area B₁ n₁ n₁) >=>
      cong boxes-raw-area B₁'=B₂' >=>
      subdivide-Boxes-preserves-raw-area B₂ n₂ n₂
