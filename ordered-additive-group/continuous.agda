{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.continuous where

open import additive-group
open import base
open import equality-path
open import functions
open import funext
open import order
open import order.minmax
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
    D⁺ : Type _
    D⁺ = Σ D (0# <_)

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

  opaque
    isContinuous-minus : isContinuous (-_)
    isContinuous-minus x i@(oi {l} {u} l<u) fx∈i@(l<-x , -x<u) =
      ∣ (oi (minus-flips-< l<u)) , (-u<x , x<-l) , g ∣
      where
      module i = OI i
      -u<x : (- i.u) < x
      -u<x = trans-<-= (minus-flips-< -x<u) minus-double-inverse
      x<-l : x < (- i.l)
      x<-l = trans-=-< (sym minus-double-inverse) (minus-flips-< l<-x)
      g : ∀ y -> y ∈OI _ -> (- y) ∈OI i
      g y (-u<y , y<-l) = (l<-y , -y<u)
        where
        l<-y : i.l < (- y)
        l<-y = trans-=-< (sym minus-double-inverse) (minus-flips-< y<-l)
        -y<u : (- y) < i.u
        -y<u = trans-<-= (minus-flips-< -u<y) minus-double-inverse

  module _ (ε⁺@(ε , 0<ε) : D⁺) (x : D) where
    εBall-at : OI D
    εBall-at = oi {l = x + (- ε)} {x + ε} (+₁-preserves-< -ε<ε)
      where
      opaque
        -ε<ε : (- ε) < ε
        -ε<ε =
          trans-<-=
            (trans-=-< (sym +-right-zero) (+-preserves-< (minus-flips-0< 0<ε) 0<ε))
            +-left-zero

    opaque
      εBall-at-∈OI : x ∈OI εBall-at
      εBall-at-∈OI = (x-ε<x , x<x+ε)
        where
        x-ε<x : (x + (- ε)) < x
        x-ε<x = trans-<-= (+₁-preserves-< (minus-flips-0< 0<ε)) +-right-zero

        x<x+ε : x < (x + ε)
        x<x+ε = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<ε)

  isContinuous'At : D -> (D -> D) -> Type _
  isContinuous'At x f =
    ∀ (ε : D⁺) -> ∃[ δ ∈ D⁺ ] (∀ y -> y ∈OI (εBall-at δ x) -> f y ∈OI (εBall-at ε (f x)))

  isContinuous' : (D -> D) -> Type _
  isContinuous' f = ∀ x -> isContinuous'At x f

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{CO : CompatibleOrderStr LO PO}}
         {{MO : MinOperationStr LO}}
         {ACM : AdditiveCommMonoid D}
         {{AG : AdditiveGroup ACM}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
  where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = PO
    D⁺ : Type _
    D⁺ = Σ D (0# <_)

  opaque
    find-εBall : (x : D) (i : OI D) -> (x ∈OI i) -> ∃[ ε ∈ D⁺ ] (εBall-at ε x ⊆OI i)
    find-εBall x i (l<x , x<u) =
      ∣ (ε , 0<ε) , (l≤x-ε , x+ε≤u) ∣
      where
      module i = OI i
      0<xu : 0# < diff x i.u
      0<xu = diff-0<⁺ x<u
      0<lx : 0# < diff i.l x
      0<lx = diff-0<⁺ l<x
      ε : D
      ε = min (diff x i.u) (diff i.l x)
      0<ε : 0# < ε
      0<ε = min-greatest-< 0<xu 0<lx
      x+ε≤u : (x + ε) ≤ i.u
      x+ε≤u = trans-≤-= (+₁-preserves-≤ min-≤-left) diff-step
      l≤x-ε : i.l ≤ (x + - ε)
      l≤x-ε =
        trans-=-≤
          (sym diff-step)
          (+₁-preserves-≤ (trans-=-≤ diff-anticommute (minus-flips-≤ min-≤-right)))


  opaque
    isContinuous'->isContinuous : {f : D -> D} -> isContinuous' f -> isContinuous f
    isContinuous'->isContinuous {f} c'f x i fx∈i =
      ∥-bind handle (find-εBall (f x) i fx∈i)
      where
      handle : Σ[ ε ∈ D⁺ ] (εBall-at ε (f x) ⊆OI i) ->
               ∃[ i2 ∈ OI D ] (x ∈OI i2 × (∀ y -> y ∈OI i2 -> (f y) ∈OI i))
      handle (ε , εBall⊆i) = ∥-map handle2 (c'f x ε)
        where
        handle2 :
          Σ[ δ ∈ D⁺ ] (∀ y -> y ∈OI (εBall-at δ x) -> f y ∈OI (εBall-at ε (f x))) ->
          Σ[ i2 ∈ OI D ] (x ∈OI i2 × (∀ y -> y ∈OI i2 -> (f y) ∈OI i))
        handle2 (δ , g) =
          (εBall-at δ x) , εBall-at-∈OI δ x ,
          (\y y∈i2 -> trans-∈OI-⊆OI (g y y∈i2) εBall⊆i)

  opaque
    isContinuous->isContinuous' : {f : D -> D} -> isContinuous f -> isContinuous' f
    isContinuous->isContinuous' {f} cf x ε =
      ∥-bind handle (cf x (εBall-at ε (f x)) (εBall-at-∈OI ε (f x)))
      where
      handle : Σ[ i2 ∈ OI D ] (x ∈OI i2 × (∀ y -> y ∈OI i2 -> (f y) ∈OI (εBall-at ε (f x)))) ->
               ∃[ δ ∈ D⁺ ] (∀ y -> y ∈OI (εBall-at δ x) -> f y ∈OI (εBall-at ε (f x)))
      handle (i2 , x∈i2 , g) = ∥-map handle2 (find-εBall x i2 x∈i2)
        where
        handle2 : Σ[ δ ∈ D⁺ ] (εBall-at δ x ⊆OI i2) ->
                  Σ[ δ ∈ D⁺ ] (∀ y -> y ∈OI (εBall-at δ x) -> f y ∈OI (εBall-at ε (f x)))
        handle2 (δ , εBall⊆i2) =
          δ , \y y∈εBall -> g y (trans-∈OI-⊆OI y∈εBall εBall⊆i2)
