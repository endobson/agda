{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.region where

open import base
open import functions
open import hlevel.base
open import hlevel.htype
open import isomorphism
open import rational-geometry.point
open import sigma.base
open import univalence

record Region (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    predicate : Point -> hProp ℓ

  contains : Point -> Type ℓ
  contains p = ⟨ predicate p ⟩

opaque
  region-ext : {ℓ : Level} {R₁ R₂ : Region ℓ} ->
    (∀ p -> (Region.contains R₁ p <-> Region.contains R₂ p)) ->
    R₁ == R₂
  region-ext {R₁ = R₁} {R₂} bi = \i -> record { predicate = \p -> path p i }
    where
    path : ∀ p -> Region.predicate R₁ p == Region.predicate R₂ p
    path p = ΣProp-path isProp-isProp
      (isoToPath (isProp->iso (proj₁ (bi p)) (proj₂ (bi p))
                   (snd (Region.predicate R₁ p))
                   (snd (Region.predicate R₂ p))))


NonOverlappingRegions : {ℓI ℓR : Level} {I : Type ℓI} -> (I -> Region ℓR) -> Type (ℓ-max ℓI ℓR)
NonOverlappingRegions {I = I} regions =
  (p : Point) (i₁ i₂ : I) ->
  Region.contains (regions i₁) p ->
  Region.contains (regions i₂) p ->
  i₁ == i₂
