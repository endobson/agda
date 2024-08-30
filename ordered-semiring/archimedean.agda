{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean where

open import additive-group
open import base
open import equality
open import nat
open import order
open import ordered-semiring
open import relation
open import semiring
open import semiring.initial
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<}
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

    opaque
      strong-archimedean-property : ∀ {a b : D} -> 0# < b -> ∃[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))
      strong-archimedean-property {a} {b} 0<b = ∥-bind handle (comparison-< _ a _ 0<b)
        where
        handle : (0# < a) ⊎ (a < b) -> ∃[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))
        handle (inj-l 0<a) = archimedean-property 0<a 0<b
        handle (inj-r a<b) = ∣ 1 , trans-<-= a<b (sym (*-left ℕ->Semiring-preserves-1# >=> *-left-one)) ∣


module _ {ℓD ℓ< : Level} (D : Type ℓD) {D< : Rel D ℓ<} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM}
         {LO : isLinearOrder D<}
         {{LOS : LinearlyOrderedSemiringStr S LO}} where
  ArchimedeanSemiringⁱ : Type (ℓ-max ℓD ℓ<)
  ArchimedeanSemiringⁱ = ArchimedeanSemiring LOS

  ArchimedeanPropertyⁱ : Type (ℓ-max ℓD ℓ<)
  ArchimedeanPropertyⁱ = ArchimedeanProperty LOS
