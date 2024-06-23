{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.instances.subspace where

open import base
open import equality-path
open import equivalence
open import metric-space
open import subset
open import subset.subspace

module _ {ℓD ℓS : Level} {D : Type ℓD} {S : Subtype D ℓS}
         {{MS : MetricSpaceStr D}} where
  instance
    MetricSpaceStr-Subspace : MetricSpaceStr (Subspace S)
    MetricSpaceStr-Subspace = record
      { distance = \(x , _) (y , _) -> distance x y
      ; 0≤distanceᵉ = \(x , _) (y , _) -> 0≤distanceᵉ x y
      ; distance-commuteᵉ = \(x , _) (y , _) -> distance-commuteᵉ x y
      ; distance-triangleᵉ = \(x , _) (y , _) (z , _) -> distance-triangleᵉ x y z
      ; path->zero-distance = \p -> path->zero-distance (cong Subspace.value p)
      ; isEquiv-path->zero-distance =
         ∘-isEquiv isEquiv-path->zero-distance (isEmbedding-Subspace-value _ _)
      }
