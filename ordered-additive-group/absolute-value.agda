{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.absolute-value where

open import additive-group
open import base
open import equality
open import equivalence
open import functions
open import hlevel.base
open import isomorphism
open import order
open import order.minmax
open import ordered-additive-group
open import ordered-additive-group.minmax
open import ordered-additive-group.negated
open import relation
open import sum
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {LO : isLinearOrder D<} {{Max : MaxOperationStr LO}}
         {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}}
         where
  private
    instance
      ILO = LO
      IACM = ACM
      PO = isLinearOrder->isPartialOrder-≯ LO
      POA = PartiallyOrderedAdditiveStr-Negated ACM LO
      CPO = CompatibleNegatedLinearOrder LO

    isSet-D : isSet D
    isSet-D = AdditiveCommMonoid.isSet-Domain ACM

  abs : D -> D
  abs x = max x (- x)

  abs-minus : {x : D} -> abs (- x) == abs x
  abs-minus {x} = cong (max (- x)) minus-double-inverse >=> max-commute

  module _ {{OA : LinearlyOrderedAdditiveStr ACM LO}} where
    abs-<0-path : {x : D} -> x < 0# -> abs x == - x
    abs-<0-path x<0 = max-<-path (trans-< x<0 (minus-flips-<0 x<0))

    abs-0<-path : {x : D} -> 0# < x -> abs x == x
    abs-0<-path 0<x = max->-path (trans-< (minus-flips-0< 0<x) 0<x)

    abs-≮0 : {x : D} -> abs x ≮ 0#
    abs-≮0 ax<0 = asym-< x<0 (trans-<-= (minus-flips-<0 -x<0) minus-double-inverse)
      where
      x<0 = trans-≤-< max-≤-left ax<0
      -x<0 = trans-≤-< max-≤-right ax<0

    abs-0≮-path : {x : D} -> 0# ≮ x -> abs x == - x
    abs-0≮-path 0≮x = max-≤-path (trans-≤ 0≮x (minus-flips-≤0 0≮x))

    abs-≮0-path : {x : D} -> x ≮ 0# -> abs x == x
    abs-≮0-path x≮0 = max-≥-path (trans-≤ (minus-flips-0≤ x≮0) x≮0)

    abs-≮ : {x : D} -> abs x ≮ x
    abs-≮ = max-≮-left

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

    abs-cases : (x y : D) -> (y <> 0#) -> abs x == y -> (x == y) ⊎ (x == (- y))
    abs-cases x y y<>0 ax=y =
      ⊎-map (\ 0<x -> sym (abs-0<-path 0<x) >=> ax=y)
            (\ x<0 -> sym minus-double-inverse >=> cong -_ (sym (abs-<0-path x<0) >=> ax=y))
            (⊎-swap x<>0)
      where
      0<ax : 0# < abs x
      0<ax = proj-¬l (subst (_<> 0#) (sym ax=y) y<>0) abs-≮0

      x<>0 : x <> 0#
      x<>0 = eqInv abs-#0-eq 0<ax

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {LO : isLinearOrder D<} {{Max : MaxOperationStr LO}}
         {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}}
         where
  private
    instance
      ILO = LO
      IACM = ACM

  module _ {ℓ≤ : Level} {D≤ : Rel D ℓ≤}
    {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
    {PO : isPartialOrder D≤}
    {{POA : PartiallyOrderedAdditiveStr ACM PO}}
    {{CO : CompatibleOrderStr LO PO}}
    where
    private
      instance
        IPO = PO

    abs-≤0-path : {x : D} -> x ≤ 0# -> abs x == - x
    abs-≤0-path x≤0 = abs-0≮-path (\ 0<x -> irrefl-< (trans-<-≤ 0<x x≤0))

    abs-0≤-path : {x : D} -> 0# ≤ x -> abs x == x
    abs-0≤-path 0≤x = abs-≮0-path (\ x<0 -> irrefl-< (trans-<-≤ x<0 0≤x))

    abs-0≤ : {x : D} -> 0# ≤ abs x
    abs-0≤ = convert-≮ abs-≮0

    abs-≤ : {x : D} -> x ≤ abs x
    abs-≤ = convert-≮ abs-≮

    abs-distrib-+ : {x y : D} -> abs (x + y) ≤ (abs x + abs y)
    abs-distrib-+ = trans-=-≤ (cong2 max refl minus-distrib-plus) max-+-swap
