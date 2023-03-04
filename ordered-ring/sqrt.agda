{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.sqrt where

open import additive-group
open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import order
open import order.minmax
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.negated
open import ordered-semiring.squares
open import ring
open import semiring
open import sigma.base
open import sum
open import truncation


module _ {ℓD ℓ< : Level} {D : Type ℓD} {{LO : LinearOrderStr D ℓ<}}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

  isSqrt : (x y : D) -> Type _
  isSqrt x y = (y ≮ 0# × y * y == x)



module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SOS : StronglyLinearlyOrderedSemiringStr S LO}} where
  private
    instance
      ILO = LO
      IS = S
      IACM = ACM
      PO = NegatedLinearOrder LO
      CPO = CompatibleNegatedLinearOrder LO
      LOA = LinearOrderTightApartnessStr LO
      TALO = TrivialApartLinearOrderStr LO
      POS = PartiallyOrderedSemiringStr-Negated S LO

    isSet-D : isSet D
    isSet-D = Semiring.isSet-Domain S



  isProp-Σsqrt : {x : D} -> isProp (Σ D (isSqrt x))
  isProp-Σsqrt (y1 , y1≮0 , y1y1=x) (y2 , y2≮0 , y2y2=x) =
    ΣProp-path (isProp× (isProp¬ _) (isSet-D _ _))
               (connected-< (y1≮y2 y1≮0 (y1y1=x >=> sym y2y2=x))
                            (y1≮y2 y2≮0 (y2y2=x >=> sym y1y1=x)))
    where
    y1≮y2 : {y1 y2 : D} -> y1 ≮ 0# -> (y1 * y1 == y2 * y2) -> y1 ≮ y2
    y1≮y2 {y1} {y2} y1≮0 y1y1=y2y2 y1<y2 = handle (*₁-fully-reflects-< y12<y11)
      where
      0<y2 = trans-≤-< y1≮0 y1<y2
      y12<y22 : (y1 * y2) < (y2 * y2)
      y12<y22 = *₂-preserves-< y1<y2 0<y2
      y12<y11 : (y1 * y2) < (y1 * y1)
      y12<y11 = trans-<-= y12<y22 (sym y1y1=y2y2)
      handle : (y2 < y1 × 0# < y1) ⊎ (y1 < y2 × y1 < 0#) -> Bot
      handle (inj-l (y2<y1 , _)) = asym-< y1<y2 y2<y1
      handle (inj-r (_ , y1<0)) = y1≮0 y1<0


  isSqrt-0< : {x y : D} -> (isSqrt x y) -> 0# < x -> 0# < y
  isSqrt-0< (0≤y , yy=x) 0<x =
    proj-¬l (proj₁ (*-reflects-<>0 (inj-r (trans-<-= 0<x (sym yy=x))))) 0≤y

  isSqrt-0≤ : {x y : D} -> (isSqrt x y) -> 0# ≤ y
  isSqrt-0≤ (0≤y , yy=x) = 0≤y

  isSqrt-* : {x y sx sy : D} -> isSqrt x sx -> isSqrt y sy -> isSqrt (x * y) (sx * sy)
  isSqrt-* {x} {y} {sx} {sy} (0≤sx , sxsx=x) (0≤sy , sysy=y) = 0≤sxsy , path
    where
    0≤sxsy : 0# ≤ (sx * sy)
    0≤sxsy = *-preserves-0≤ 0≤sx 0≤sy

    path : (sx * sy) * (sx * sy) == x * y
    path = *-swap >=> cong2 _*_ sxsx=x sysy=y

  module _ {{Max : MaxOperationStr LO}} {{AG : AdditiveGroup ACM}} where

    isSqrt-square : {x y : D} -> isSqrt (x * x) y -> y == abs x
    isSqrt-square {x} {y} (0≤y , yy=xx) =
      connected-< y≮ax ax≮y
      where
      y≮ax : y ≮ abs x
      y≮ax y<ax = irrefl-path-< (yy=xx >=> abs-square) yy<axax
        where
        yy<axax : (y * y) < (abs x * abs x)
        yy<axax = squares-ordered⁺ 0≤y y<ax

      ax≮y : abs x ≮ y
      ax≮y ax<y = irrefl-path-< (sym (yy=xx >=> abs-square)) axax<yy
        where
        axax<yy : (abs x * abs x) < (y * y)
        axax<yy = squares-ordered⁺ abs-≮0 ax<y
