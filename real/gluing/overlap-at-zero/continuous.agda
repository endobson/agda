{-# OPTIONS --cubical --safe --exact-split #-}

module real.gluing.overlap-at-zero.continuous where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import heyting-field.instances.real
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import rational
open import real
open import real.arithmetic.rational
open import real.distance
open import real.gluing.overlap-at-zero
open import real.gluing.overlap-at-zero.extension
open import real.order
open import real.rational
open import real.subspace
open import relation
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import subset
open import subset.subspace
open import truncation


module _ (f : (x : ℝ≤≥0) -> ℝ) (cont-f@(isContinuous-cons cf) : isContinuous f) where
  private
    fℚ : ℚ -> ℝ
    fℚ q = f (ℚ->ℝ≤≥0 q)

    0∈ = (ℚ->ℝ≤≥0 0#)

    ef : ℝ -> ℝ
    ef = extend-≤≥0 f cont-f

    opaque
      isContinuous⁺ : {x : ℝ} -> 0# < x -> isContinuousAt ef x
      isContinuous⁺ {x} 0<x ε⁺@(ε , 0<ε) = ∥-map handle (cf x∈ ε⁺)
        where
        x∈ : ℝ≤≥0
        x∈ = (x , ∣ inj-r (weaken-< 0<x) ∣)
        handle :
          Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ≤≥0) -> (εClose δ x y) -> εClose ε⁺ (f x∈) (f y∈)) ->
          Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (ef x) (ef y))
        handle ((δ , 0<δ) , δ-close) = ((δ2 , 0<δ2) , δ2-close)
          where
          δ2 : ℝ
          δ2 = min δ x
          0<δ2 : 0# < δ2
          0<δ2 = min-greatest-< 0<δ 0<x
          δ2-close : (∀ y -> (distance x y < δ2) -> distance (ef x) (ef y) < ε)
          δ2-close y dxy<δ2 = trans-=-< d-path dfxfy<ε
            where
            δ2≤d0x : δ2 ≤ diff 0# x
            δ2≤d0x = trans-≤-= min-≤-right (sym diff-step >=> +-left-zero)
            0<y : 0# < y
            0<y = distance-diff-<₂ (trans-<-≤ (trans-=-< (distance-commuteᵉ y x) dxy<δ2) δ2≤d0x)
            y∈ : ℝ≤≥0
            y∈ = (y , ∣ inj-r (weaken-< 0<y) ∣)
            dfxfy<ε : distance (f x∈) (f y∈) < ε
            dfxfy<ε = δ-close y∈ (trans-<-≤ dxy<δ2 min-≤-left)
            fx-path : ef x == (f x∈)
            fx-path = isExtension-extend-≤≥0 f cont-f x∈
            fy-path : ef y == (f y∈)
            fy-path = isExtension-extend-≤≥0 f cont-f y∈
            d-path : distance (ef x) (ef y) == distance (f x∈) (f y∈)
            d-path = cong2 distance fx-path fy-path

    opaque
      isContinuous⁻ : {x : ℝ} -> x < 0# -> isContinuousAt ef x
      isContinuous⁻ {x} x<0 ε⁺@(ε , 0<ε) = ∥-map handle (cf x∈ ε⁺)
        where
        x∈ : ℝ≤≥0
        x∈ = (x , ∣ inj-l (weaken-< x<0) ∣)
        handle :
          Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ≤≥0) -> (εClose δ x y) -> εClose ε⁺ (f x∈) (f y∈)) ->
          Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (ef x) (ef y))
        handle ((δ , 0<δ) , δ-close) = ((δ2 , 0<δ2) , δ2-close)
          where
          δ2 : ℝ
          δ2 = min δ (- x)
          0<δ2 : 0# < δ2
          0<δ2 = min-greatest-< 0<δ (minus-flips-<0 x<0)
          δ2-close : (∀ y -> (distance x y < δ2) -> distance (ef x) (ef y) < ε)
          δ2-close y dxy<δ2 = trans-=-< d-path dfxfy<ε
            where
            δ2≤dx0 : δ2 ≤ diff x 0#
            δ2≤dx0 = trans-≤-= min-≤-right (sym +-left-zero)
            y<0 : y < 0#
            y<0 = distance-diff-<₁ (trans-<-≤ dxy<δ2 δ2≤dx0)
            y∈ : ℝ≤≥0
            y∈ = (y , ∣ inj-l (weaken-< y<0) ∣)
            dfxfy<ε : distance (f x∈) (f y∈) < ε
            dfxfy<ε = δ-close y∈ (trans-<-≤ dxy<δ2 min-≤-left)
            fx-path : ef x == (f x∈)
            fx-path = isExtension-extend-≤≥0 f cont-f x∈
            fy-path : ef y == (f y∈)
            fy-path = isExtension-extend-≤≥0 f cont-f y∈
            d-path : distance (ef x) (ef y) == distance (f x∈) (f y∈)
            d-path = cong2 distance fx-path fy-path

  opaque
    isContinuous-extend-≤≥0 : isContinuous ef
    isContinuous-extend-≤≥0 .isContinuous.at x ε⁺@(ε , 0<ε) =
      ∥-bind2 handle0 f0-ε/2<f0 f0<f0+ε/2
      where
      Ans : Type₁
      Ans = ∃[ (δ , _) ∈ ℝ⁺ ] (∀ y -> distance x y < δ -> distance (ef x) (ef y) < ε)

      ε/2 : ℝ
      ε/2 = ε * 1/2
      0<ε/2 : 0# < ε/2
      0<ε/2 = *-preserves-0< 0<ε 0<1/2
      f0<f0+ε/2 : f 0∈ < (f 0∈ + ε/2)
      f0<f0+ε/2 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<ε/2)
      f0-ε/2<f0 : (f 0∈ + (- ε/2)) < f 0∈
      f0-ε/2<f0 = trans-<-= (+₁-preserves-< (minus-flips-0< 0<ε/2)) +-right-zero

      handle0 : (f 0∈ + (- ε/2)) ℝ<' f 0∈  -> f 0∈ ℝ<' (f 0∈ + ε/2) -> Ans
      handle0 (ℝ<'-cons l f0εU-l f0L-l) (ℝ<'-cons u f0U-u f0εL-u) =
        ∥-bind2 handle0' l<f0 f0<u
        where
        l<f0 : ℚ->ℝ l < f 0∈
        l<f0 = L->ℝ< f0L-l
        f0<u : f 0∈ < ℚ->ℝ u
        f0<u = U->ℝ< f0U-u
        handle0' : ℚ->ℝ l ℝ<' f 0∈ -> f 0∈ ℝ<' (ℚ->ℝ u) -> Ans
        handle0' (ℝ<'-cons l' lU-l' f0L-l') (ℝ<'-cons u' f0U-u' uL-u') =
          ∥-bind handle (isContinuous->isContinuousℚ cont-f .isContinuousℚ.at 0∈ (ε' , 0<ε'))
          where
          l<l' : l < l'
          l<l' = U->ℚ< lU-l'
          u'<u : u' < u
          u'<u = L->ℚ< uL-u'
          l'<f0 : ℚ->ℝ l' < f 0∈
          l'<f0 = L->ℝ< f0L-l'
          f0<u' : f 0∈ < ℚ->ℝ u'
          f0<u' = U->ℝ< f0U-u'
          ε' : ℝ
          ε' = min (diff (ℚ->ℝ l') (f 0∈)) (diff (f 0∈) (ℚ->ℝ u'))
          0<ε' : 0# < ε'
          0<ε' = min-greatest-< (diff-0<⁺ l'<f0) (diff-0<⁺ f0<u')
          handle : Σ[ (δ , _) ∈ ℚ⁺ ] (∀ (x∈@(x , _) : Subspace ℝ≤≥0S) ->
                                        distance 0# x < ℚ->ℝ δ -> distance (f 0∈) (f x∈) < ε') ->
                   Ans
          handle ((δ , 0<δ) , δ-close) =
            ∥-bind handle2 (split-distance<ε 0# x (ℚ->ℝ δ , ℚ->ℝ-preserves-< 0<δ))
            where
            handle2 : Tri⊎ (x < 0#) (distance 0# x < (ℚ->ℝ δ)) (0# < x) -> Ans
            handle2 (tri⊎-< x<0) = isContinuous⁻ x<0 ε⁺
            handle2 (tri⊎-> 0<x) = isContinuous⁺ 0<x ε⁺
            handle2 (tri⊎-= d0x<δ) = ∥-bind handle3 d0x<δ
              where
              handle3 : distance 0# x ℝ<' (ℚ->ℝ δ) -> Ans
              handle3 (ℝ<'-cons δ' d0xU-δ' δL-δ') =
                ∣ (ℚ->ℝ δ2 , ℚ->ℝ-preserves-< 0<δ2) , δ2-close ∣
                where
                δ2 : ℚ
                δ2 = diff δ' δ
                0<δ2 : 0# < δ2
                0<δ2 = diff-0<⁺ (L->ℚ< δL-δ')
                d0x<δ' : distance 0# x < ℚ->ℝ δ'
                d0x<δ' = U->ℝ< d0xU-δ'

                δ2-close : ∀ y -> distance x y < ℚ->ℝ δ2 -> distance (ef x) (ef y) < ε
                δ2-close y dxy<δ2 = dxy<ε
                  where
                  module _ (z : ℝ) (d0z<δ : distance 0# z < ℚ->ℝ δ) where
                    opaque
                      unfolding extend-≤≥0 isContinuous-extend-≤≥0

                      u'-bound : (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ ->
                                 Real.U (fℚ t) u'
                      u'-bound t d0tU-δ = ℝ<->U ft<u'
                        where
                        df0ft<ε' : distance (f 0∈) (fℚ t) < ε'
                        df0ft<ε' = δ-close (ℚ->ℝ≤≥0 t) (U->ℝ< d0tU-δ)
                        ft<u' : (fℚ t) < ℚ->ℝ u'
                        ft<u' = distance-diff-<₁ (trans-<-≤ df0ft<ε' min-≤-right)

                      l'-bound : (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ ->
                                 Real.L (fℚ t) l'
                      l'-bound t d0tU-δ = ℝ<->L l'<ft
                        where
                        df0ft<ε' : distance (f 0∈) (fℚ t) < ε'
                        df0ft<ε' = δ-close (ℚ->ℝ≤≥0 t) (U->ℝ< d0tU-δ)
                        l'<ft : ℚ->ℝ l' < fℚ t
                        l'<ft =
                          distance-diff-<₂ (trans-<-≤ (trans-=-< (distance-commuteᵉ (fℚ t) (fℚ 0#))
                                                                 df0ft<ε')
                                                      min-≤-left)

                      fzU-u : Real.U (ef z) u
                      fzU-u = ∣ tri⊎-= (u' , u'<u , (δ , 0<δ) , ℝ<->U d0z<δ ,
                                        u'-bound) ∣

                      fzL-l : Real.L (ef z) l
                      fzL-l = ∣ tri⊎-= (l' , l<l' , (δ , 0<δ) , ℝ<->U d0z<δ ,
                                        l'-bound) ∣


                    fz<f0+ε/2 : (ef z) < (f 0∈ + ε/2)
                    fz<f0+ε/2 = ∣ ℝ<'-cons u fzU-u f0εL-u ∣

                    f0-ε/2<fz : (f 0∈ + (- ε/2)) < (ef z)
                    f0-ε/2<fz = ∣ ℝ<'-cons l f0εU-l fzL-l ∣

                    dif0z<ε/2 : diff (f 0∈) (ef z) < ε/2
                    dif0z<ε/2 =
                      trans-<-= (+₂-preserves-< fz<f0+ε/2)
                                (+-left +-commute >=> +-assoc >=> +-right +-inverse >=> +-right-zero)

                    -dif0z<ε/2 : (- (diff (f 0∈) (ef z))) < ε/2
                    -dif0z<ε/2 =
                      trans-=-< (sym diff-anticommute)
                        (trans-<-=
                          (+₁-preserves-< (minus-flips-< f0-ε/2<fz))
                          (+-right (sym diff-anticommute) >=> diff-step))

                    d0z<ε/2 : distance (f 0∈) (ef z) < ε/2
                    d0z<ε/2 = max-least-< dif0z<ε/2 -dif0z<ε/2

                  d0y<δ : distance 0# y < ℚ->ℝ δ
                  d0y<δ =
                    trans-≤-< (distance-triangleᵉ 0# _ y)
                      (trans-<-= (+-preserves-< d0x<δ' dxy<δ2)
                        (sym ℚ->ℝ-preserves-+ >=> cong ℚ->ℝ diff-step))

                  d0x<ε/2 : distance (f 0∈) (ef x) < ε/2
                  d0x<ε/2 = d0z<ε/2 x d0x<δ
                  d0y<ε/2 : distance (f 0∈) (ef y) < ε/2
                  d0y<ε/2 = d0z<ε/2 y d0y<δ

                  dxy<ε : distance (ef x) (ef y) < ε
                  dxy<ε =
                    trans-≤-< (distance-triangleᵉ (ef x) _ (ef y))
                      (trans-=-< (+-left (distance-commuteᵉ (ef x) (fℚ 0#)))
                        (trans-<-= (+-preserves-< d0x<ε/2 d0y<ε/2)
                                   +-/2-path))
