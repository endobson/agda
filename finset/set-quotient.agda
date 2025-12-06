{-# OPTIONS --cubical --safe --exact-split #-}

module finset.set-quotient where

open import base
open import decision
open import discrete
open import equality-path
open import equivalence
open import finset
open import finset.finitely-indexed
open import functions
open import graph.simple
open import graph.simple.strc
open import hlevel.base
open import isomorphism
open import relation
open import relation.closure
open import set-quotient
open import set-quotient.equivalence
open import truncation
open import univalence

private
  module _ {ℓA ℓR : Level} {A : Type ℓA} {R : Rel A ℓR}
           (isFinSet-A : isFinSet A)
           (isProp-R : isPropValued R) (isEquivRel-R : isEquivRel R)
           (isDecidable-R : Decidable2 R) where

    private
      convert : A -> A / R
      convert a = [ a ]

      isSurjective-convert : isSurjective convert
      isSurjective-convert = SetQuotientElim.elimProp (\_ -> squash) (\a -> ∣ a , refl ∣)

      Discrete-A/R : Discrete (A / R)
      Discrete-A/R = Discrete-SetQuotient isProp-R isEquivRel-R isDecidable-R

      instance
        Discrete'-A/R : Discrete' (A / R)
        Discrete'-A/R = record { f = Discrete-A/R }

    isFinSet-SetQuotient-raw : isFinSet (A / R)
    isFinSet-SetQuotient-raw =
      FinitelyIndexed-Discrete->isFinSet
        (A , isFinSet-A) convert isSurjective-convert



module _ {ℓA ℓR : Level} {A : Type ℓA} {R : Rel A ℓR}
         (isFinSet-A : isFinSet A)
         (isDecidable-R : Decidable2 R) where
  private
    instance
      DA : Discrete' A
      DA = record { f = isFinSet->Discrete isFinSet-A }

    R' : Rel A (ℓ-max ℓA ℓR)
    R' a₁ a₂ = ∥ SymmetricReflexiveClosure R a₁ a₂ ∥

    isDecidable-R' : Decidable2 R'
    isDecidable-R' a₁ a₂ = handle (isDecidable-R a₁ a₂) (isDecidable-R a₂ a₁) (decide-= a₁ a₂)
      where
      handle : Dec (R a₁ a₂) -> Dec (R a₂ a₁) -> Dec (a₁ == a₂) -> Dec (R' a₁ a₂)
      handle (yes r)  _        _       = yes (∣ closure-rel r ∣)
      handle (no ¬r₁) (yes r)  _       = yes (∣ closure-sym (closure-rel r) ∣)
      handle (no ¬r₁) (no ¬r₂) (yes p) = yes (subst (R' a₁) p ∣ closure-refl ∣)
      handle (no ¬r₁) (no ¬r₂) (no ¬p) = no (unsquash isPropBot ∘ ∥-map (handle2 ¬r₁ ¬r₂ ¬p))
        where
        handle2 : {a₁ a₂ : A} -> ¬ (R a₁ a₂) -> ¬ (R a₂ a₁) -> a₁ != a₂ ->
                  ¬ (SymmetricReflexiveClosure R a₁ a₂)
        handle2 ¬r _ _ (closure-rel r) = (¬r r)
        handle2 ¬r₁ ¬r₂ ¬p (closure-sym r) = handle2 ¬r₂ ¬r₁ (¬p ∘ sym) r
        handle2 _ _ ¬p (closure-refl) = ¬p refl

    G : Graph ℓA (ℓ-max ℓA ℓR)
    G = record
      { V = A
      ; E = R'
      ; isFinSet-V = isFinSet-A
      ; isProp-E = \_ _ -> squash
      ; dec-E = isDecidable-R'
      ; refl-E = \v -> ∣ closure-refl ∣
      ; sym-E = \v₁ v₂ -> ∥-map closure-sym
      }

    dec₁ : ∀ v₁ v₂ -> Dec (∥ SymmetricTransitiveReflexiveClosure R' v₁ v₂ ∥)
    dec₁ = decide-STRC G

    simplify : ∀ v₁ v₂ -> Iso (∥ SymmetricTransitiveReflexiveClosure R' v₁ v₂ ∥)
                              (∥ SymmetricTransitiveReflexiveClosure R v₁ v₂ ∥)
    simplify v₁ v₂ = isProp->iso (∥-bind for) (∥-map back) squash squash
      where

      lift₁ : ∀ {v₁} {v₂} ->
            SymmetricReflexiveClosure R v₁ v₂ ->
            SymmetricTransitiveReflexiveClosure R v₁ v₂
      lift₁ (closure-rel r) = (closure-rel r)
      lift₁ (closure-refl) = closure-refl
      lift₁ (closure-sym r) = (closure-sym (lift₁ r))


      for : ∀ {v₁} {v₂} ->
            SymmetricTransitiveReflexiveClosure R' v₁ v₂ ->
            ∥ SymmetricTransitiveReflexiveClosure R v₁ v₂ ∥
      for (closure-rel r) = ∥-map lift₁ r
      for (closure-refl) = ∣ closure-refl ∣
      for (closure-sym r) = ∥-map closure-sym (for r)
      for (closure-trans r₁ r₂) = ∥-map2 closure-trans (for r₁) (for r₂)

      back : ∀ {v₁} {v₂} ->
             SymmetricTransitiveReflexiveClosure R v₁ v₂ ->
             SymmetricTransitiveReflexiveClosure R' v₁ v₂
      back (closure-rel r) = (closure-rel (∣ closure-rel r ∣))
      back (closure-refl) = closure-refl
      back (closure-sym r) = closure-sym (back r)
      back (closure-trans r₁ r₂) = closure-trans (back r₁) (back r₂)


    dec₂ : ∀ v₁ v₂ -> Dec (∥ SymmetricTransitiveReflexiveClosure R v₁ v₂ ∥)
    dec₂ v₁ v₂ = dec-map (Iso.fun (simplify v₁ v₂)) (Iso.inv (simplify v₁ v₂)) (dec₁ v₁ v₂)

    eq-rel : isEquivRel (\v₁ v₂ -> (∥ SymmetricTransitiveReflexiveClosure R v₁ v₂ ∥))
    eq-rel = equivRel (∣ closure-refl ∣) (∥-map closure-sym) (∥-map2 closure-trans)


    isFinSet-R₂ : isFinSet (A / (\v₁ v₂ -> (∥ SymmetricTransitiveReflexiveClosure R v₁ v₂ ∥)))
    isFinSet-R₂ = isFinSet-SetQuotient-raw isFinSet-A (\_ _ -> squash) eq-rel dec₂

  opaque
    isFinSet-SetQuotient : isFinSet (A / R)
    isFinSet-SetQuotient =
      subst isFinSet (ua (SetQuotient-∥-eq _ _ >eq> SetQuotient-STRC-eq _ _)) isFinSet-R₂
