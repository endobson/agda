{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.continuous where

open import additive-group
open import base
open import equality-path
open import functions
open import funext
open import order
open import order.continuous
open import order.interval
open import ordered-additive-group
open import relation
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D}
         {{AG : AdditiveGroup ACM}}
         {LO : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         where
  private
    instance
      IACM = ACM
      ILO = LO

  opaque
    isContinuous-+₁ : ∀ (x : D) -> isContinuous (x +_)
    isContinuous-+₁ x y i (l<x+y , x+y<u) =
      ∣ i2 , (-x+l<y , y<-x+u) , f ∣
      where
      module i = OI i
      -x+l<y : (- x + i.l) < y
      -x+l<y = trans-<-= (+₁-preserves-< l<x+y)
                         (sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero)
      y<-x+u : y < (- x + i.u)
      y<-x+u = trans-=-< (sym (sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero))
                         (+₁-preserves-< x+y<u)
      i2 : OI D
      i2 = oi (trans-< -x+l<y y<-x+u)

      f : (z : D) -> z ∈OI i2 -> (x + z) ∈OI i
      f z (-x+l<z , z<-x+u) =
        trans-=-< (sym (sym +-assoc >=> +-left (+-inverse) >=> +-left-zero))
                  (+₁-preserves-< -x+l<z) ,
        trans-<-= (+₁-preserves-< z<-x+u)
                  (sym +-assoc >=> +-left (+-inverse) >=> +-left-zero)

  opaque
    isContinuous-+₂ : ∀ (x : D) -> isContinuous (_+ x)
    isContinuous-+₂ x =
      subst isContinuous (funExt (\y -> +-commute)) (isContinuous-+₁ x)
