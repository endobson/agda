{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.initial where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import functions
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import ordered-additive-group.negated
open import ordered-semiring
open import ordered-semiring.instances.nat
open import ordered-semiring.negated
open import relation
open import semiring
open import semiring.initial
open import semiring.instances.nat
open import sigma.base
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {LO : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}} where
  private
    instance
      IACM = ACM
      IS = S
      ILO = LO
      IPO = isLinearOrder->isPartialOrder-≯ LO
      IPOA = PartiallyOrderedAdditiveStr-Negated ACM LO
      IPOS = PartiallyOrderedSemiringStr-Negated S LO
      ICO = CompatibleNegatedLinearOrder LO

    ℕ->D : ℕ -> D
    ℕ->D = ℕ->Semiring

    semiʰ : Semiringʰ ℕ->D
    semiʰ = ∃!-prop ∃!ℕ->Semiring
    module semiʰ = Semiringʰ semiʰ

  module _ (0<1 : D< 0# 1#) where
    private
      ℕ->D-suc< : (n : ℕ) -> ℕ->D n < ℕ->D (suc n)
      ℕ->D-suc< zero = subst2 _<_ (sym semiʰ.preserves-0#) (sym semiʰ.preserves-1#) 0<1
      ℕ->D-suc< (suc n) =
        subst2 _<_ (sym (semiʰ.preserves-+ _ _)) (sym (semiʰ.preserves-+ _ _))
                   (+₁-preserves-< (ℕ->D-suc< n))

      ℕ->D-0≤ : (n : ℕ) -> 0# ≤ ℕ->D n
      ℕ->D-0≤ = ℕ->Semiring-elim refl-≤ (weaken-< 0<1) p+
        where
        p+ : (a b : D) -> 0# ≤ a -> 0# ≤ b -> 0# ≤ (a + b)
        p+ _ _ = +-preserves-0≤

      ℕ->D-preserves-0< : {n : ℕ} -> 0 < n -> 0# < ℕ->D n
      ℕ->D-preserves-0< 0<n = Nat⁺Elim-1+ p1 p+ (_ , <->Pos' 0<n)
        where
        p1 : 0# < ℕ->D 1
        p1 = trans-<-= 0<1 (sym semiʰ.preserves-1#)
        p+ : (a b : Nat⁺) -> 0# < (ℕ->D ⟨ a ⟩) -> 0# < (ℕ->D ⟨ b ⟩) -> 0# < (ℕ->D ⟨ (a +⁺ b) ⟩)
        p+ _ _ 0<a 0<b = trans-<-= (+-preserves-0< 0<a 0<b) (sym (semiʰ.preserves-+ _ _))

      ℕ->D-preserves-≤ : {a b : ℕ} -> a ≤ b -> ℕ->D a ≤ ℕ->D b
      ℕ->D-preserves-≤ {a} {b} (i , p) =
        trans-=-≤ (sym +-left-zero)
          (trans-≤-= (+₂-preserves-≤ (ℕ->D-0≤ i))
                     ((sym (semiʰ.preserves-+ _ _)) >=> cong ℕ->D p))

      ℕ->D-preserves-< : {a b : ℕ} -> a < b -> ℕ->D a < ℕ->D b
      ℕ->D-preserves-< sa≤b = trans-<-≤ (ℕ->D-suc< _) (ℕ->D-preserves-≤ sa≤b)


    ∃!ℕ->LinearlyOrderedSemiring : ∃! (ℕ -> D) LinearlyOrderedSemiringʰ
    ∃!ℕ->LinearlyOrderedSemiring = (ℕ->D , prop) , unique
      where
      abstract
        prop : LinearlyOrderedSemiringʰ ℕ->D
        prop = record
          { semiringʰ = semiʰ
          ; <ʰ = record
            { preserves-< = ℕ->D-preserves-<
            }
          }

        unique : ∀ (g : (Σ (ℕ -> D) LinearlyOrderedSemiringʰ)) -> (ℕ->D , prop) == g
        unique (f , record { semiringʰ = fʰ }) =
          ΣProp-path isProp-LinearlyOrderedSemiringʰ (∃!-unique ∃!ℕ->Semiring f fʰ)
