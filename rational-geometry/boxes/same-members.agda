{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.same-members where

open import base
open import equality-path
open import equivalence
open import finset
open import functions.family
open import hlevel.base
open import isomorphism
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import sigma.base
open import truncation

module _ {ℓ : Level} (B₁ B₂ : Boxes ℓ)
  (o₁ : hasNoOverlap B₁) (o₂ : hasNoOverlap B₂)
  (f₁ : ∀ (i : Boxes.I B₁) -> ∥ fiber (Boxes.box B₂) (Boxes.box B₁ i) ∥)
  (f₂ : ∀ (i : Boxes.I B₂) -> ∥ fiber (Boxes.box B₁) (Boxes.box B₂ i) ∥)
  where
  private
    module B₁ = Boxes B₁
    module B₂ = Boxes B₂

    isProp-fiber₁ : ∀ b -> isProp (fiber (Boxes.box B₁) b)
    isProp-fiber₁ b (i₁ , p₁) (i₂ , p₂) =
      ΣProp-path (isSet-Box _ _)
        (o₁ (Box.bottom-left b) i₁ i₂
            (subst (\p -> b₁.contains p)
                   (cong Box.bottom-left p₁)
                   b₁.bottom-left∈region)
            (subst (\p -> b₂.contains p)
                   (cong Box.bottom-left p₂)
                   b₂.bottom-left∈region))
      where
      module b₁ = Box (B₁.box i₁)
      module b₂ = Box (B₁.box i₂)

    isProp-fiber₂ : ∀ b -> isProp (fiber (Boxes.box B₂) b)
    isProp-fiber₂ b (i₁ , p₁) (i₂ , p₂) =
      ΣProp-path (isSet-Box _ _)
        (o₂ (Box.bottom-left b) i₁ i₂
            (subst (\p -> b₁.contains p)
                   (cong Box.bottom-left p₁)
                   b₁.bottom-left∈region)
            (subst (\p -> b₂.contains p)
                   (cong Box.bottom-left p₂)
                   b₂.bottom-left∈region))
      where
      module b₁ = Box (B₂.box i₁)
      module b₂ = Box (B₂.box i₂)

    for : ∀ b -> (fiber B₁.box b) -> (fiber B₂.box b)
    for b (i₁ , p₁) =
      unsquash (isProp-fiber₂ b) (∥-map (\ (i₂ , p₂) -> (i₂ , p₂ >=> p₁)) (f₁ i₁))
    back : ∀ b -> (fiber B₂.box b) -> (fiber B₁.box b)
    back b (i₁ , p₁) =
      unsquash (isProp-fiber₁ b) (∥-map (\ (i₂ , p₂) -> (i₂ , p₂ >=> p₁)) (f₂ i₁))

    fiber-eq : ∀ b -> (fiber (Boxes.box B₁) b) ≃ (fiber (Boxes.box B₂) b)
    fiber-eq b = isoToEquiv (isProp->iso (for b) (back b) (isProp-fiber₁ b) (isProp-fiber₂ b))

    box-path : (Boxes.I B₁ , Boxes.box B₁) == (Boxes.I B₂ , Boxes.box B₂)
    box-path = eqFun (FiberEq≃FamilyPath _ _) fiber-eq

  opaque
    same-members->same-boxes : B₁ == B₂
    same-members->same-boxes i = record
      { Index = fst (box-path i) , isFinSet-Index i
      ; box = snd (box-path i)
      }
      where
      isFinSet-Index : PathP (\i -> isFinSet (fst (box-path i))) (snd (Boxes.Index B₁)) (snd (Boxes.Index B₂))
      isFinSet-Index = isProp->PathP (\_ -> isProp-isFinSet)
