{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.union-boxes where

open import base
open import equality-path
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.region
open import rational-geometry.point
open import rational-geometry.boxes.area.raw
open import finset
open import sigma.base
open import finsum
open import truncation
open import hlevel.base
open import finite-commutative-monoid.sigma
open import finset.instances.sigma


union-Boxes : {ℓ₁ ℓ₂ : Level} -> ((I , _) : FinSet ℓ₁) -> (I -> Boxes ℓ₂) -> Boxes (ℓ-max ℓ₁ ℓ₂)
union-Boxes {ℓ₁} {ℓ₂} (I , isFinSet-I) Bs = record
  { Index = I' , isFinSet-Σ isFinSet-I (\i -> snd (Boxes.Index (Bs i)))
  ; box = \ (i₁ , i₂) -> Boxes.box (Bs i₁) i₂
  }
  where
  I' : Type (ℓ-max ℓ₁ ℓ₂)
  I' = Σ[ i ∈ I ] (Boxes.I (Bs i))

raw-area-union-Boxes :
  {ℓ₁ ℓ₂ : Level} -> (Index@(I , _) : FinSet ℓ₁) -> (Bs : I -> Boxes ℓ₂) ->
  boxes-raw-area (union-Boxes Index Bs) ==
  finiteSumᵉ Index (\i -> boxes-raw-area (Bs i))
raw-area-union-Boxes Index Bs = finiteMerge-Σ _ _ _ _


hasNoOverlap-union-Boxes : {ℓ₁ ℓ₂ : Level} ->
  (Index@(I , _) : FinSet ℓ₁) -> (Bs : I -> Boxes ℓ₂) ->
  (∀ i -> NonOverlappingRegions (\j -> Box.region (Boxes.box (Bs i) j))) ->
  NonOverlappingRegions (\i -> Boxes.region (Bs i)) ->
  hasNoOverlap (union-Boxes Index Bs)
hasNoOverlap-union-Boxes Index@(I , _) Bs box-overlap boxes-overlap p
  (i₁ , j₁) (i₂ , j₂) p∈r₁ p∈r₂ = \k -> fst (total-path k) , fst (snd (total-path k))
  where
  B : Boxes _
  B = union-Boxes Index Bs
  I' : Type _
  I' = Boxes.I B
  isSet-I' : isSet I'
  isSet-I' = isFinSet->isSet (snd (Boxes.Index B))

  i-path : i₁ == i₂
  i-path = boxes-overlap p i₁ i₂ (∣ j₁ , p∈r₁ ∣) (∣ j₂ , p∈r₂ ∣)

  isProp-inner : ∀ {i} -> isProp (Σ[ j ∈ Boxes.I (Bs i) ] (Box.contains (Boxes.box (Bs i) j) p))
  isProp-inner {i} (j₁ , p₁) (j₂ , p₂) =
    ΣProp-path (\{j} -> (snd (Region.predicate (Box.region (Boxes.box (Bs i) j)) p)))
      (box-overlap i p j₁ j₂ p₁ p₂)

  total-path :
    Path (Σ[ i ∈ I ] Σ[ j ∈ Boxes.I (Bs i) ] (Box.contains (Boxes.box (Bs i) j) p))
      (i₁ , j₁ , p∈r₁) (i₂ , j₂ , p∈r₂)
  total-path = ΣProp-path isProp-inner i-path
