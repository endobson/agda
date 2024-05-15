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


  module _ {ε : D} (0<ε : 0# < ε) (x : D) where
    εball-at : OI D
    εball-at = oi {l = x + (- ε)} {x + ε} (+₁-preserves-< -ε<ε)
      where
      opaque
        -ε<ε : (- ε) < ε
        -ε<ε =
          trans-<-=
            (trans-=-< (sym +-right-zero) (+-preserves-< (minus-flips-0< 0<ε) 0<ε))
            +-left-zero

    opaque
      εball-at-∈OI : x ∈OI εball-at
      εball-at-∈OI = (x-ε<x , x<x+ε)
        where
        x-ε<x : (x + (- ε)) < x
        x-ε<x = trans-<-= (+₁-preserves-< (minus-flips-0< 0<ε)) +-right-zero

        x<x+ε : x < (x + ε)
        x<x+ε = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<ε)

  isContinuous'At : D -> (D -> D) -> Type _
  isContinuous'At x f =
    ∀ (ε : D) -> (0<ε : 0# < ε) ->
    ∃[ δ ∈ D ] Σ[ 0<δ ∈ (0# < δ) ] (∀ y -> y ∈OI (εball-at 0<δ x) -> f y ∈OI (εball-at 0<ε (f x)))

  isContinuous' : (D -> D) -> Type _
  isContinuous' f = ∀ x -> isContinuous'At x f
