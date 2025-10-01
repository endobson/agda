{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.remove-overlap where

open import base
open import relation
open import equivalence.base
open import equality-path
open import decision
open import finset
open import functions
open import sum
open import hlevel.pi
open import hlevel.base
open import truncation
open import set-quotient
open import finset.set-quotient
open import rational-geometry.boxes.box
open import rational-geometry.region
open import rational-geometry.boxes.same-members
open import rational-geometry.boxes.base

module _ {ℓ : Level} (B : Boxes ℓ)
  (decide-overlap : ∀ i₁ i₂ ->
    (Boxes.box B i₁ == Boxes.box B i₂) ⊎
    (∀ p -> Box.contains (Boxes.box B i₁) p -> Box.contains (Boxes.box B i₂) p -> Bot))
  where

  private
    module B = Boxes B

    _~_ : Rel B.I ℓ-zero
    _~_ i₁ i₂ = Boxes.box B i₁ == Boxes.box B i₂

    I : Type ℓ
    I = B.I / _~_

    boxes : I -> Box
    boxes = SetQuotientElim.rec isSet-Box B.box (\_ _ p -> p)

    -- DO not submit replace with decidable equality for boxes
    decide-~ : ∀ i₁ i₂ -> Dec (i₁ ~ i₂)
    decide-~ i₁ i₂ = either yes (no ∘ convert) (decide-overlap i₁ i₂)
      where
      convert : (∀ p -> Box.contains (B.box i₁) p -> Box.contains (B.box i₂) p -> Bot) ->
                ¬ (B.box i₁ == B.box i₂)
      convert ¬point path =
        ¬point b.bottom-left
               b.bottom-left∈region
               (subst (\b -> Box.contains b b.bottom-left)
                      path b.bottom-left∈region)
        where
        module b = Box (B.box i₁)

    B₂ : Boxes ℓ
    B₂ = record
      { Index = I , isFinSet-SetQuotient (snd B.Index) decide-~
      ; box = boxes
      }

    hasNoOverlap-B₂ : hasNoOverlap B₂
    hasNoOverlap-B₂ p =
      SetQuotientElim.elimProp2 (\i₁ i₂ -> (isPropΠ2 (\_ _ -> squash/ i₁ i₂)))
        (\i₁ i₂ p∈b₁ p∈b₂ ->
          either (eq/ _ _) (\ ¬p -> bot-elim (¬p p p∈b₁ p∈b₂))
            (decide-overlap i₁ i₂))


    mere-fibers : ∀ i -> ∥ fiber B.box (boxes i) ∥
    mere-fibers = SetQuotientElim.elimProp (\_ -> squash) (\i -> ∣ i , refl ∣)

    mere-fibers' : ∀ i -> ∥ fiber boxes (B.box i) ∥
    mere-fibers' i = ∣ [ i ] , refl ∣

    maybe-same-boxes : (hasNoOverlap B) -> B₂ == B
    maybe-same-boxes hasNoOverlap-B =
      same-members->same-boxes B₂ B hasNoOverlap-B₂ hasNoOverlap-B mere-fibers mere-fibers'



    same-region : Boxes.region B₂ == Boxes.region B
    same-region = region-ext (\p -> forward p , backward p)
      where

      forward : ∀ p -> Boxes.contains B₂ p -> Boxes.contains B p
      forward p = ∥-bind (\ (i₂ , p∈b) -> handle i₂ p∈b)
        where
        handle : ∀ (i₂ : I) -> Box.contains (boxes i₂) p -> Boxes.contains B p
        handle =
          SetQuotientElim.elimProp
            (\i -> isPropΠ (\_ -> snd (Region.predicate (Boxes.region B) p)))
            (\i p∈b -> ∣ i , p∈b ∣)

      backward : ∀ p -> Boxes.contains B p -> Boxes.contains B₂ p
      backward p = ∥-map (\ (i , p∈b) -> [ i ] , p∈b )


  remove-overlaps/decidable :
    Σ[ B₂ ∈ Boxes ℓ ] (hasNoOverlap B₂ × (∀ i -> ∥ fiber B.box (Boxes.box B₂ i) ∥) ×
                       Boxes.region B₂ == Boxes.region B ×
                       ((hasNoOverlap B) -> B₂ == B))
  remove-overlaps/decidable = B₂ , hasNoOverlap-B₂ , mere-fibers , same-region , maybe-same-boxes
