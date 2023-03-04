{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.absolute-value where

open import base
open import equality
open import order
open import equivalence
open import hlevel
open import functions
open import ordered-semiring
open import ordered-semiring.negated
open import ordered-semiring.squares
open import ordered-ring
open import order.minmax
open import additive-group
open import semiring
open import truncation
open import sum
open import isomorphism
open import ring


module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {{Max : MaxOperationStr LO}}
         {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}} {{S : Semiring ACM}}
         where
  private
    instance
      ILO = LO
      IACM = ACM
      PO = NegatedLinearOrder LO
      CPO = CompatibleNegatedLinearOrder LO

    isSet-D : isSet D
    isSet-D = Semiring.isSet-Domain S

  abs : D -> D
  abs x = max x (- x)


  module _ {{OS : LinearlyOrderedSemiringStr S LO}} where
    abs-<0-path : {x : D} -> x < 0# -> abs x == - x
    abs-<0-path x<0 = max-<-path (trans-< x<0 (minus-flips-<0 x<0))

    abs-0<-path : {x : D} -> 0# < x -> abs x == x
    abs-0<-path 0<x = max->-path (trans-< (minus-flips-0< 0<x) 0<x)

    abs-≮0 : {x : D} -> abs x ≮ 0#
    abs-≮0 ax<0 = asym-< x<0 (trans-<-= (minus-flips-<0 -x<0) minus-double-inverse)
      where
      x<0 = trans-≤-< max-≤-left ax<0
      -x<0 = trans-≤-< max-≤-right ax<0

    abs-#0-eq : {x : D} -> (x <> 0#) ≃ (0# < abs x)
    abs-#0-eq {x} = isoToEquiv (isProp->iso forward backward isProp-<> isProp-<)
      where
      forward : (x <> 0#) -> (0# < abs x)
      forward (inj-l x<0) = trans-<-= 0<-x (sym (abs-<0-path x<0))
        where
        0<-x = minus-flips-<0 x<0
      forward (inj-r 0<x) = trans-<-= 0<x (sym (abs-0<-path 0<x))

      backward : (0# < abs x) -> (x <> 0#)
      backward 0<ax = unsquash isProp-<> (∥-bind handle (comparison-< 0# x (abs x) 0<ax))
        where
        handle : (0# < x) ⊎ (x < abs x) -> ∥ (x <> 0#) ∥
        handle (inj-l 0<x) = ∣ inj-r 0<x ∣
        handle (inj-r x<ax) = ∥-map handle2 (comparison-< x 0# (- x) x<-x)
          where
          ax=-x = max-<-left-path x<ax
          x<-x : x < (- x)
          x<-x = trans-<-= x<ax ax=-x
          handle2 : (x < 0#) ⊎ (0# < (- x)) -> x <> 0#
          handle2 (inj-l x<0) = (inj-l x<0)
          handle2 (inj-r 0<-x) = (inj-l (trans-=-< (sym minus-double-inverse) (minus-flips-0< 0<-x)))

    abs-zero-eq : {x : D} -> (x == 0#) ≃ (abs x == 0#)
    abs-zero-eq {x} = isoToEquiv (isProp->iso forward backward (isSet-D _ _) (isSet-D _ _))
      where
      forward : (x == 0#) -> (abs x == 0#)
      forward p = cong abs p >=> cong (max 0#) minus-zero >=> max-idempotent

      backward : (abs x == 0#) -> (x == 0#)
      backward p = connected-< (irrefl-path-< (sym p) ∘ eqFun abs-#0-eq ∘ inj-l)
                               (irrefl-path-< (sym p) ∘ eqFun abs-#0-eq ∘ inj-r)


  module _ {{OS : LinearlyOrderedSemiringStr S LO}}
           {{SOS : StronglyLinearlyOrderedSemiringStr S LO}} where
    private
      instance
        POS = PartiallyOrderedSemiringStr-Negated S LO

    abs-0≮-path : {x : D} -> 0# ≮ x -> abs x == - x
    abs-0≮-path 0≮x = max-≤-path (trans-≤ 0≮x (minus-flips-≤0 0≮x))

    abs-≮0-path : {x : D} -> x ≮ 0# -> abs x == x
    abs-≮0-path x≮0 = max-≥-path (trans-≤ (minus-flips-0≤ x≮0) x≮0)

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
