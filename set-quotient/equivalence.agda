{-# OPTIONS --cubical --safe --exact-split #-}

module set-quotient.equivalence where

open import base
open import equality-path
open import equivalence
open import isomorphism
open import relation.closure
open import set-quotient
open import truncation

module _ {ℓA ℓR : Level} (A : Type ℓA) (R : Rel A ℓR) where
  SetQuotient-∥-eq : (A / (\a₁ a₂ -> ∥ R a₁ a₂ ∥)) ≃ (A / R)
  SetQuotient-∥-eq = isoToEquiv (iso f g fg gf)
    where
    f : (A / (\a₁ a₂ -> ∥ R a₁ a₂ ∥)) -> (A / R)
    f = SetQuotientElim.rec squash/ (\a -> [ a ])
      (\a₁ a₂ r -> unsquash (squash/ [ a₁ ] [ a₂ ]) (∥-map (eq/ a₁ a₂) r))

    g : (A / R) -> (A / (\a₁ a₂ -> ∥ R a₁ a₂ ∥))
    g = SetQuotientElim.rec squash/ (\a -> [ a ]) (\a₁ a₂ r -> eq/ a₁ a₂ ∣ r ∣)

    fg : ∀ x -> f (g x) == x
    fg = SetQuotientElim.elimProp (\e -> squash/ (f (g e)) e) (\_ -> refl)
    gf : ∀ x -> g (f x) == x
    gf = SetQuotientElim.elimProp (\e -> squash/ (g (f e)) e) (\_ -> refl)


  SetQuotient-STRC-eq : (A / (SymmetricTransitiveReflexiveClosure R)) ≃ (A / R)
  SetQuotient-STRC-eq = isoToEquiv (iso f g fg gf)
    where
    S = SymmetricTransitiveReflexiveClosure R

    rec : {a₁ a₂ : A} -> S a₁ a₂ -> [ a₁ ] == [ a₂ ]
    rec (closure-rel r) = eq/ _ _ r
    rec (closure-refl) = refl
    rec (closure-sym s) = sym (rec s)
    rec (closure-trans s₁ s₂) = (rec s₁) >=> (rec s₂)

    f : A / S -> A / R
    f = SetQuotientElim.rec squash/ (\a -> [ a ]) (\_ _ -> rec)

    g : A / R -> A / S
    g = SetQuotientElim.rec squash/ (\a -> [ a ]) (\a₁ a₂ r -> eq/ a₁ a₂ (closure-rel r))

    fg : ∀ x -> f (g x) == x
    fg = SetQuotientElim.elimProp (\e -> squash/ (f (g e)) e) (\_ -> refl)
    gf : ∀ x -> g (f x) == x
    gf = SetQuotientElim.elimProp (\e -> squash/ (g (f e)) e) (\_ -> refl)
