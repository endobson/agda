{-# OPTIONS --cubical --safe --exact-split #-}

module real.gluing.overlap-at-zero.extension where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
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
open import ordered-additive-group.instances.real
open import rational
open import rational.open-interval
open import real
open import real.distance
open import real.gluing.overlap-at-zero
open import real.open-interval
open import real.order
open import real.rational
open import real.subspace
open import relation
open import subset.subspace
open import truncation


module _ (f : (x : ℝ≤≥0) -> ℝ) (cont-f@(isContinuous-cons cf) : isContinuous f) where
  private
    fℚ : ℚ -> ℝ
    fℚ q = f (ℚ->ℝ≤≥0 q)

    0∈ = (ℚ->ℝ≤≥0 0#)

  opaque
    unfolding extend-≤≥0

    isExtension-extend-≤≥0 : ∀ (x∈@(x , _) : ℝ≤≥0) -> extend-≤≥0 f cont-f x == f x∈
    isExtension-extend-≤≥0 x∈@(x , _) = sym (ℝ∈Iℚ->path _ _ g)
      where
      fx : ℝ
      fx = (f x∈)
      efx : ℝ
      efx = (extend-≤≥0 f cont-f x)
      module fx = Real fx
      module efx = Real efx

      fx-path : {p1 p2 : ∥ (x ≤ 0#) ⊎ (0# ≤ x) ∥} -> f (x , p1) == f (x , p2)
      fx-path = cong f (Subspace-path refl)

      g : (i : Iℚ) -> ℝ∈Iℚ fx i -> ℝ∈Iℚ efx i
      g i@(Iℚ-cons l u l<u) (fxL-l , fxU-u) =
        unsquash (isProp-ℝ∈Iℚ efx i)
          (∥-bind2 handle0 (fx.isUpperOpen-L l fxL-l) (fx.isLowerOpen-U u fxU-u))
        where

        only-εcase : ((ε , _) : ℝ⁺) -> (distance 0# x < ε -> ∥ ℝ∈Iℚ efx i ∥) -> ∥ ℝ∈Iℚ efx i ∥
        only-εcase ε⁺@(ε , _) εcase = ∥-bind handle (split-distance<ε 0# x ε⁺)
          where
          handle : Tri⊎ (x < 0#) (distance 0# x < ε) (0# < x) -> ∥ ℝ∈Iℚ efx i ∥
          handle (tri⊎-< x<0) =
            ∣ (∣ tri⊎-< (ℝ<->U x<0 , subst (\fx -> Real.L fx l) fx-path fxL-l) ∣) ,
              (∣ tri⊎-< (ℝ<->U x<0 , subst (\fx -> Real.U fx u) fx-path fxU-u) ∣) ∣
          handle (tri⊎-> 0<x) =
            ∣ (∣ tri⊎-> (ℝ<->L 0<x , subst (\fx -> Real.L fx l) fx-path fxL-l) ∣) ,
              (∣ tri⊎-> (ℝ<->L 0<x , subst (\fx -> Real.U fx u) fx-path fxU-u) ∣) ∣
          handle (tri⊎-= d0x<ε) = εcase d0x<ε

        handle0 : Σ[ l' ∈ ℚ ] (l < l' × fx.L l') -> Σ[ u' ∈ ℚ ] (u' < u × fx.U u') ->
                  ∥ ℝ∈Iℚ efx i ∥
        handle0 (l' , l<l' , fxL-l') (u' , u'<u , fxU-u') = ∥-bind handle (cf x∈ ε⁺)
          where
          l'<u' : l' < u'
          l'<u' = ℝ-bounds->ℚ< fx fxL-l' fxU-u'

          ε1 ε2 : ℝ
          ε1 = diff (ℚ->ℝ l') fx
          ε2 = diff fx (ℚ->ℝ u')
          0<ε1 : 0# < ε1
          0<ε1 = diff-0<⁺ (L->ℝ< fxL-l')
          0<ε2 : 0# < ε2
          0<ε2 = diff-0<⁺ (U->ℝ< fxU-u')
          ε : ℝ
          ε = min ε1 ε2
          0<ε : 0# < ε
          0<ε = min-greatest-< 0<ε1 0<ε2
          ε⁺ : ℝ⁺
          ε⁺ = ε , 0<ε

          handle :
            Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ≤≥0 ) -> εClose δ x y -> εClose ε⁺ (f x∈) (f y∈)) ->
            ∥ ℝ∈Iℚ efx i ∥
          handle (δ⁺@(δ , 0<δ) , close) = only-εcase δ⁺ handle2
            where
            handle2 : (εClose δ⁺ 0# x) -> ∥ ℝ∈Iℚ efx i ∥
            handle2 d0x<δ = ∥-bind handle3 (diff-0<⁺ d0x<δ)
              where
              handle3 : (0# ℝ<' diff (distance 0# x) δ) -> ∥ ℝ∈Iℚ efx i ∥
              handle3 (ℝ<'-cons δ2 0U-δ2 diff-dxδL-δ2) =
                only-εcase (ℚ->ℝ δ2 , ℚ->ℝ-preserves-< 0<δ2) handle4
                where
                0<δ2 : 0# < δ2
                0<δ2 = U->ℚ< 0U-δ2
                d+δ2<δ : (distance 0# x + ℚ->ℝ δ2) < δ
                d+δ2<δ = trans-<-= (+₁-preserves-< (L->ℝ< diff-dxδL-δ2)) diff-step

                closeLU : ∀ (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ2 ->
                            Real.L (fℚ t) l' × Real.U (fℚ t) u'
                closeLU t dtU-δ = ℝ<->L l<ft , ℝ<->U ft<u
                  where
                  dt<δ2 : (distance 0# (ℚ->ℝ t)) < ℚ->ℝ δ2
                  dt<δ2 = U->ℝ< dtU-δ

                  dxt<δ : distance x (ℚ->ℝ t) < δ
                  dxt<δ =
                    trans-≤-< (distance-triangleᵉ x _ (ℚ->ℝ t))
                      (trans-< (+₁-preserves-< dt<δ2)
                        (trans-=-< (+-left (distance-commuteᵉ x _))
                          d+δ2<δ))

                  dfxft<ε : distance (f x∈) (fℚ t) < ε
                  dfxft<ε = close (ℚ->ℝ≤≥0 t) dxt<δ

                  ft<u : (fℚ t) < ℚ->ℝ u'
                  ft<u = distance-diff-<₁ (trans-<-≤ dfxft<ε min-≤-right)

                  l<ft : ℚ->ℝ l' < (fℚ t)
                  l<ft = distance-diff-<₂ (trans-=-< (distance-commuteᵉ (fℚ t) (f x∈))
                                                     (trans-<-≤ dfxft<ε min-≤-left))

                handle4 : (distance 0# x < ℚ->ℝ δ2) -> ∥ ℝ∈Iℚ efx i ∥
                handle4 dx<δ2 =
                  ∣ (∣ tri⊎-= (l' , l<l' , (δ2 , 0<δ2) , ℝ<->U dx<δ2 ,
                               \t dU-t -> proj₁ (closeLU t dU-t)) ∣) ,
                    (∣ tri⊎-= (u' , u'<u , (δ2 , 0<δ2) , ℝ<->U dx<δ2 ,
                               \t dU-t -> proj₂ (closeLU t dU-t)) ∣) ∣
