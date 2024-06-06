{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-field.archimedean where

open import additive-group
open import apartness
open import base
open import equality
open import heyting-field
open import nat
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-field
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.initial
open import relation
open import ring
open import semiring
open import semiring.initial
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D# : Rel D ℓD}
         {A : isTightApartness D#}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {LOS : LinearlyOrderedSemiringStr S LO}
         {{NT : NonTrivialLinearlyOrderedSemiringStr LOS}}
         {{AS : ArchimedeanSemiring LOS}}
         {AG : AdditiveGroup ACM}
         {R : Ring S AG}
         {{F : Field R A}}
         {{AL : ApartLinearOrderStr A LO}}
         where
  private
    instance
      IS = S
      ILO = LO
      IACM = ACM
      ILOA = LOA
      ILOS = LOS

    D⁺ : Type (ℓ-max ℓD ℓ<)
    D⁺ = Σ D (0# <_)

  small-1/ℕ : ((x , _) : D⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m < x)
  small-1/ℕ (x , 0<x) = ∥-map handle (archimedean-property 0<1 0<x)
    where
    handle : Σ[ m ∈ Nat ] (1# < (ℕ->Semiring m * x)) ->
             Σ[ m ∈ Nat⁺ ] (1/ℕ m < x)
    handle (m , 1<mx) = (m2 , tt) , 1/m2<x
      where
      m2 = suc m
      m2⁺ : Nat⁺
      m2⁺ = m2 , tt
      m<m2 : ℕ->Semiring m < ℕ->Semiring m2
      m<m2 = ℕ->Semiring-preserves-< refl-≤
      1<m2x : 1# < (ℕ->Semiring m2 * x)
      1<m2x = trans-< 1<mx (*₂-preserves-< m<m2 0<x)
      1/m2<x : 1/ℕ m2⁺ < x
      1/m2<x =
        trans-=-< (sym *-right-one)
          (trans-<-= (*₁-preserves-< (0<1/ℕ m2⁺) 1<m2x)
            (sym *-assoc >=> *-left (*-commute >=> (∃!-prop (∃!1/ℕ m2⁺))) >=> *-left-one))
