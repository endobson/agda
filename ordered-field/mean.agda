{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-field.mean where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import heyting-field
open import hlevel
open import integral-domain.instances.heyting-field
open import nat
open import nat.order
open import order
open import ordered-additive-group
open import ordered-ring
open import ordered-field
open import ordered-semiring
open import ordered-semiring.initial
open import ordered-semiring.integral-domain
open import relation
open import ring
open import semiring
open import semiring.initial
open import sigma.base
open import sum
open import truncation

private
  variable
    ℓD ℓ< : Level

module _ {D : Type ℓD} {D# : Rel D ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {LO : isLinearOrder D<}
         {R : Ring S AG} {A : isTightApartness D#}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {LOS : LinearlyOrderedSemiringStr S LO}
         {{NTO : NonTrivialLinearlyOrderedSemiringStr LOS}}
         {{F : Field R A}}
         {{AL : ApartLinearOrderStr A LO}}
         where
  private
    module F = Field F
    module R = Ring R
    instance
      ILOS = LOS
      IACM = ACM
      IAG = AG
      IS = S
      ILO = LO
      IR = R
      IA = A
      IID = IntegralDomain-Field
      ISOS = StronglyLinearlyOrderedSemiringStr-IntegralDomain


  mean : D -> D -> D
  mean x y = 1/2 * (x + y)

  mean-commute : {x y : D} -> mean x y == mean y x
  mean-commute = *-right +-commute

  mean-+-1/2-diff : {x y : D} -> mean x y + (1/2 * (diff x y)) == y
  mean-+-1/2-diff {x} {y} =
    sym *-distrib-+-left >=>
    cong (1/2 *_)
      (+-left +-commute >=>
       +-assoc >=>
       +-right diff-step) >=>
    *-distrib-+-left >=>
    1/2-path

  mean-minus-1/2-diff : {x y : D} -> mean x y + (- (1/2 * (diff x y))) == x
  mean-minus-1/2-diff =
    +-cong mean-commute (sym minus-extract-right >=> *-right (sym diff-anticommute)) >=>
    mean-+-1/2-diff

  diff-mean : {x y : D} -> diff (mean x y) y == 1/2 * diff x y
  diff-mean = +-left (sym mean-+-1/2-diff) >=> +-assoc >=> diff-step

  diff-mean' : {x y : D} -> diff x (mean x y) == 1/2 * diff x y
  diff-mean' = +-right (cong -_ (sym mean-minus-1/2-diff) >=> sym diff-anticommute) >=> diff-step

  module _ {x y : D} (x<y : x < y) where
    private
      0<d = (*-preserves-0< 0<1/2 (diff-0<⁺ x<y))
      -d<0 = minus-flips-0< 0<d

    mean-<₁ : x < mean x y
    mean-<₁ = trans-=-< (sym mean-minus-1/2-diff) (trans-<-= (+₁-preserves-< -d<0) +-right-zero)

    mean-<₂ : mean x y < y
    mean-<₂ = trans-=-< (sym +-right-zero) (trans-<-= (+₁-preserves-< 0<d) mean-+-1/2-diff)

  module _ {ℓ≤ : Level} {D≤ : Rel D ℓ≤} {PO : isPartialOrder D≤}
           {{POA : PartiallyOrderedAdditiveStr ACM PO}}
           {{POS : PartiallyOrderedSemiringStr S PO}}
           {{CO : CompatibleOrderStr LO PO}} where
    private
      instance
        IPO = PO
    module _ {x y : D} (x≤y : x ≤ y) where
      private
        0≤d = (*-preserves-0≤ (weaken-< 0<1/2) (diff-0≤⁺ x≤y))
        -d≤0 = minus-flips-0≤ 0≤d

      mean-≤₁ : x ≤ mean x y
      mean-≤₁ = trans-=-≤ (sym mean-minus-1/2-diff) (trans-≤-= (+₁-preserves-≤ -d≤0) +-right-zero)

      mean-≤₂ : mean x y ≤ y
      mean-≤₂ = trans-=-≤ (sym +-right-zero) (trans-≤-= (+₁-preserves-≤ 0≤d) mean-+-1/2-diff)
