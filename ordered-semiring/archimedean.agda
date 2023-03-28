{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean where

open import base
open import additive-group
open import semiring
open import semiring.initial
open import order
open import ordered-semiring
open import truncation
open import nat

module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM}
         {LO : LinearOrderStr D ℓ<}
          where
  private
    instance
      IACM = ACM
      IS = S
      ILO = LO

  module _ (LOS : LinearlyOrderedSemiringStr S LO) where
    ArchimedeanProperty : Type (ℓ-max ℓD ℓ<)
    ArchimedeanProperty = ∀ {a b : D} -> 0# < a -> 0# < b -> ∃[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))

  record ArchimedeanSemiring (LOS : LinearlyOrderedSemiringStr S LO) : Type (ℓ-max ℓD ℓ<) where
    field
      prop : ArchimedeanProperty LOS

  module _ {LOS : LinearlyOrderedSemiringStr S LO} {{Arch : ArchimedeanSemiring LOS}} where
    archimedean-property : ArchimedeanProperty LOS
    archimedean-property = ArchimedeanSemiring.prop useⁱ

module _ {ℓD ℓ< : Level} (D : Type ℓD) {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM}
         {LO : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S LO}} where
  ArchimedeanSemiringⁱ : Type (ℓ-max ℓD ℓ<)
  ArchimedeanSemiringⁱ = ArchimedeanSemiring LOS

  ArchimedeanPropertyⁱ : Type (ℓ-max ℓD ℓ<)
  ArchimedeanPropertyⁱ = ArchimedeanProperty LOS
