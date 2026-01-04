{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.mean where

open import additive-group
open import base
open import equality-path
open import nat
open import order
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.natural-reciprocal
open import semiring
open import semiring.initial
open import semiring.mean
open import semiring.natural-reciprocal

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}}
         {{_ : ℕ->Semiring-Op D}}
         {{_ : 1/ℕ-Op D}}
         {{LO : isLinearOrder D<}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{NTO : NonTrivialLinearlyOrderedSemiringStr LOS}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
  where
  module _ {x y : D} (x<y : x < y) where
    opaque
      mean-<₁ : x < mean x y
      mean-<₁ = trans-=-< (sym (*-distrib-+-right >=> +-/2-path))
                          (*₂-preserves-< (+₁-preserves-< x<y) (0<1/ℕ 2⁺))

      mean-<₂ : mean x y < y
      mean-<₂ = trans-<-= (*₂-preserves-< (+₂-preserves-< x<y) (0<1/ℕ 2⁺))
                          (*-distrib-+-right >=> +-/2-path)


module _ {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}}
         {{_ : ℕ->Semiring-Op D}}
         {{_ : 1/ℕ-Op D}}
         {{LO : isLinearOrder D<}}
         {{PO : isPartialOrder D≤}}
         {{CO : CompatibleOrderStr LO PO}}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
         {{SPOA : StronglyPartiallyOrderedAdditiveStr ACM PO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
  where
  module _ {x y : D} (x≤y : x ≤ y) where
    mean-≤₁ : x ≤ mean x y
    mean-≤₁ = trans-=-≤ (sym (*-distrib-+-right >=> +-/2-path))
                        (*₂-preserves-≤ (+₁-preserves-≤ x≤y) (0≤1/ℕ 2⁺))

    mean-≤₂ : mean x y ≤ y
    mean-≤₂ = trans-≤-= (*₂-preserves-≤ (+₂-preserves-≤ x≤y) (0≤1/ℕ 2⁺))
                        (*-distrib-+-right >=> +-/2-path)
