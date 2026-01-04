{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean.small where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality-path
open import nat
open import nat.exponentiation
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.initial
open import ordered-semiring.natural-reciprocal
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import semiring.instances.nat
open import semiring.natural-reciprocal
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}} {{S : Semiring ACM}}
         {{_ : ℕ->Semiring-Op D}}
         {{_ : 1/ℕ-Op D}}
         {{LO : isLinearOrder D<}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{NT : NonTrivialLinearlyOrderedSemiringStr LOS}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
         {{AS : ArchimedeanSemiring LOS}}
         where
  private
    D⁺ : Type (ℓ-max ℓD ℓ<)
    D⁺ = Σ D (0# <_)

  opaque
    small-1/ℕ : ((x , _) : D⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m < x)
    small-1/ℕ (x , 0<x) = ∥-map handle (archimedean-property 0<1 0<x)
      where
      handle : Σ[ m ∈ Nat ] (1# < (ℕ->Semiring m * x)) ->
               Σ[ m ∈ Nat⁺ ] (1/ℕ m < x)
      handle (m , 1<mx) = (m2 , tt) , 1/m2<x
        where
        m2 : Nat
        m2 = suc m
        m2⁺ : Nat⁺
        m2⁺ = m2 , tt
        1<m2x : 1# < (ℕ->Semiring m2 * x)
        1<m2x = trans-< 1<mx (*₂-preserves-< (ℕ->Semiring-preserves-< refl-≤) 0<x)
        1/m2<x : 1/ℕ m2⁺ < x
        1/m2<x =
          trans-=-< (sym *-right-one)
            (trans-<-= (*₁-preserves-< (0<1/ℕ m2⁺) 1<m2x)
              (sym *-assoc >=> *-left (*-commute >=> (∃!-prop (∃!1/ℕ m2⁺))) >=> *-left-one))

    small-1/2^ℕ : ((x , _) : D⁺) -> ∃[ m ∈ Nat ] (1/2 ^ℕ m) < x
    small-1/2^ℕ x⁺@(x , 0<x) = ∥-map handle (small-1/ℕ x⁺)
      where
      handle : Σ[ m ∈ Nat⁺ ] 1/ℕ m < x -> Σ[ m ∈ Nat ] (1/2 ^ℕ m) < x
      handle (m⁺@(m , _) , 1/m<x) =
        m , trans-=-< 1/2^ℕ-path (trans-< (1/ℕ-flips-< _ _ (2^n-large m)) 1/m<x)
        where
        1/2^ℕ-path : 1/2 ^ℕ m == 1/ℕ (2⁺ ^⁺ m)
        1/2^ℕ-path = sym (∃!-unique (∃!1/ℕ (2⁺ ^⁺ m)) _ inner-path)
          where
          inner-path : ℕ->Semiring (2 ^ℕ m) * (1/2 ^ℕ m) == 1#
          inner-path =
            *-left (Semiringʰ-preserves-^ℕ ℕ->Semiringʰ m) >=>
            sym (^ℕ-distrib-*-right m) >=>
            cong (_^ℕ m) (ℕ-1/ℕ-path 2⁺) >=>
            ^ℕ-preserves-1# m
