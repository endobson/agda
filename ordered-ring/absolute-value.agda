{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.absolute-value where

open import additive-group
open import base
open import equality
open import equivalence
open import order
open import order.minmax
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.negated
open import ordered-semiring
open import ordered-semiring.negated
open import ordered-semiring.squares
open import ring
open import semiring
open import sum
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {{Max : MaxOperationStr LO}}
         {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}} {{S : Semiring ACM}}
         where
  private
    instance
      ILO = LO
      IACM = ACM
      PO = NegatedLinearOrder LO
      CPO = CompatibleNegatedLinearOrder LO

  module _
     {{OA : LinearlyOrderedAdditiveStr ACM LO}}
     {{OS : LinearlyOrderedSemiringStr S LO}}
     {{SOS : StronglyLinearlyOrderedSemiringStr S LO}}
     where
    private
      instance
        POS = PartiallyOrderedSemiringStr-Negated S LO
        POA = PartiallyOrderedAdditiveStr-Negated ACM LO

    abs-distrib-* : {x y : D} -> abs (x * y) == abs x * abs y
    abs-distrib-* {x} {y} = connected-< case1 case2
      where
      standard-cases : (x <> 0#) -> (y <> 0#) -> abs (x * y) == abs x * abs y
      standard-cases (inj-l x<0) (inj-l y<0) =
        abs-0<-path (*-flips-<0 x<0 y<0) >=>
        sym minus-extract-both >=>
        cong2 _*_ (sym (abs-<0-path x<0)) (sym (abs-<0-path y<0))
      standard-cases (inj-l x<0) (inj-r 0<y) =
        abs-<0-path (*₂-preserves-<0 x<0 0<y) >=>
        sym minus-extract-left >=>
        cong2 _*_ (sym (abs-<0-path x<0)) (sym (abs-0<-path 0<y))
      standard-cases (inj-r 0<x) (inj-l y<0) =
        abs-<0-path (*₁-preserves-<0 0<x y<0) >=>
        sym minus-extract-right >=>
        cong2 _*_ (sym (abs-0<-path 0<x)) (sym (abs-<0-path y<0))
      standard-cases (inj-r 0<x) (inj-r 0<y) =
        abs-0<-path (*-preserves-0< 0<x 0<y) >=>
        cong2 _*_ (sym (abs-0<-path 0<x)) (sym (abs-0<-path 0<y))

      case1 : abs (x * y) ≮ (abs x * abs y)
      case1 axy<axay =
        irrefl-path-< (standard-cases (eqInv abs-#0-eq 0<ax) (eqInv abs-#0-eq 0<ay)) axy<axay
        where
        0<axay : 0# < (abs x * abs y)
        0<axay =
          unsquash isProp-< (∥-map (\s -> proj-¬l s abs-≮0) (comparison-< _ _ _ axy<axay))
        0<ax : 0# < abs x
        0<ax = *₂-reflects-0< 0<axay abs-≮0
        0<ay : 0# < abs y
        0<ay = *₁-reflects-0< abs-≮0 0<axay

      case2 : abs (x * y) ≯ (abs x * abs y)
      case2 axy>axay =
        irrefl-path-< (sym (standard-cases x<>0 y<>0)) axy>axay
        where
        0≤axay = *-preserves-0≤ abs-≮0 abs-≮0
        0<axy : 0# < abs (x * y)
        0<axy =
          unsquash isProp-< (∥-map (\s -> proj-¬l s 0≤axay) (comparison-< _ _ _ axy>axay))
        xy<>0 : (x * y) <> 0#
        xy<>0 = eqInv abs-#0-eq 0<axy
        x<>0 = proj₁ (*-reflects-<>0 xy<>0)
        y<>0 = proj₂ (*-reflects-<>0 xy<>0)

    abs-square : {x : D} -> x * x == abs x * abs x
    abs-square {x} = sym (abs-≮0-path square-≮0) >=> abs-distrib-*
