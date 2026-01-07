{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.base where

open import base
open import finset
open import rational-geometry.boxes.box
open import rational-geometry.point
open import rational-geometry.region
open import truncation

record Boxes (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Index : FinSet ℓ

  I : Type ℓ
  I = ⟨ Index ⟩

  field
    box : I -> Box

  region : Region ℓ
  region = record { predicate = \x -> P x , squash }
    where
    P : Point -> Type ℓ
    P x = ∃[ i ∈ I ] (Region.contains (Box.region (box i)) x)

  contains : Pred Point ℓ
  contains = Region.contains region

hasNoOverlap : {ℓ : Level} -> Boxes ℓ -> Type ℓ
hasNoOverlap B = NonOverlappingRegions (\i -> Box.region (Boxes.box B i))
