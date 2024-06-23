{-# OPTIONS --cubical --safe --exact-split #-}

module real.gluing.overlap-at-zero where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import heyting-field.instances.rational
open import hlevel
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
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-field.mean
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.open-interval
open import real
open import real.arithmetic.rational
open import real.continuous.bounds
open import real.distance
open import real.open-interval
open import real.order
open import real.rational
open import real.subspace
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import subset.subspace
open import truncation

ℚ->ℝ≤≥0 : ℚ -> ℝ≤≥0
ℚ->ℝ≤≥0 q = ℚ->ℝ q , case (split-< 0# q) of
  \{ (inj-l 0<q) -> ∣ inj-r (ℚ->ℝ-preserves-≤ (weaken-< 0<q)) ∣
   ; (inj-r q≤0) -> ∣ inj-l (ℚ->ℝ-preserves-≤ q≤0) ∣
   }

private
  0∈ : Subspace ℝ≤≥0S
  0∈ = 0# , ∣ inj-l refl-≤ ∣

module _ (f : (x : ℝ≤≥0) -> ℝ) (cont-f@(isContinuous-cons cf) : isContinuous f) (x : ℝ) where
  private
    f0 : ℝ
    f0 = f 0∈
    module x = Real x
    module f0 = Real f0
    contℚ-f : isContinuousℚ f
    contℚ-f = isContinuous->isContinuousℚ cont-f

    f⁺ : (x : ℝ) -> 0# < x -> ℝ
    f⁺ x 0<x = f (x , ∣ inj-r (weaken-< 0<x) ∣)
    f⁻ : (x : ℝ) -> x < 0# -> ℝ
    f⁻ x x<0 = f (x , ∣ inj-l (weaken-< x<0) ∣)
    fℚ : ℚ -> ℝ
    fℚ q = f (ℚ->ℝ≤≥0 q)

    L'0< : Pred ℚ ℓ-zero
    L'0< q = Σ[ xL ∈ x.L 0# ] (Real.L (f⁺ x (L->ℝ< xL)) q)

    L'<0 : Pred ℚ ℓ-zero
    L'<0 q = Σ[ xU ∈ x.U 0# ] (Real.L (f⁻ x (U->ℝ< xU)) q)

    L'ε : Pred ℚ ℓ-zero
    L'ε q =
      Σ[ q' ∈ ℚ ] (q < q' ×
        Σ[ (δ , _) ∈ ℚ⁺ ] (Real.U (distance 0# x) δ ×
          ∀ t -> Real.U (distance 0# (ℚ->ℝ t)) δ -> Real.L (fℚ t) q'))

    L' : Pred ℚ ℓ-zero
    L' q = Tri⊎ (L'<0 q) (L'ε q) (L'0< q)

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥

    U'0< : Pred ℚ ℓ-zero
    U'0< q = Σ[ xL ∈ x.L 0# ] (Real.U (f⁺ x (L->ℝ< xL)) q)

    U'<0 : Pred ℚ ℓ-zero
    U'<0 q = Σ[ xU ∈ x.U 0# ] (Real.U (f⁻ x (U->ℝ< xU)) q)

    U'ε : Pred ℚ ℓ-zero
    U'ε q =
      Σ[ q' ∈ ℚ ] (q' < q ×
        Σ[ (δ , _) ∈ ℚ⁺ ] (Real.U (distance 0# x) δ ×
          ∀ t -> Real.U (distance 0# (ℚ->ℝ t)) δ -> Real.U (fℚ t) q'))

    U' : Pred ℚ ℓ-zero
    U' q = Tri⊎ (U'<0 q) (U'ε q) (U'0< q)

    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥

    fx-path : {p1 p2 : ∥ (x ≤ 0#) ⊎ (0# ≤ x) ∥} -> f (x , p1) == f (x , p2)
    fx-path = cong f (Subspace-path refl)

    Inhabited-LU : (Inhabited L) × (Inhabited U)
    Inhabited-LU =
      unsquash (isProp× squash squash)
        (∥-bind handle (isContinuousℚ.at contℚ-f 0∈ (1# , 0<1)))
      where
      Ans : Type₀
      Ans = ∥ Inhabited L × Inhabited U ∥
      handle : Σ[ (δ , _) ∈ ℚ⁺ ] (∀ (y∈@(y , _) : ℝ≤≥0) ->
                                     distance 0# y < ℚ->ℝ δ -> distance (f 0∈) (f y∈) < 1#) ->
               Ans
      handle (δ⁺@(δ , 0<δ) , close) =
        ∥-bind handle2 (split-distance<ε 0# x (ℚ->ℝ δ , ℚ->ℝ-preserves-< 0<δ))
        where
        handle2 : Tri⊎ (x < 0#) (distance 0# x < ℚ->ℝ δ) (0# < x) -> Ans
        handle2 (tri⊎-< x<0) = ∥-bind2 handle3 (Real.Inhabited-L fx) (Real.Inhabited-U fx)
          where
          fx : ℝ
          fx = (f⁻ x x<0)
          handle3 : Σ[ q ∈ ℚ ] (Real.L fx q) -> Σ[ q ∈ ℚ ] (Real.U fx q) -> Ans
          handle3 (q1 , fxL-q1) (q2 , fxU-q2) =
            ∣ (∣ q1 , ∣ tri⊎-< (ℝ<->U x<0 , subst (\x -> Real.L x q1) fx-path fxL-q1) ∣ ∣) ,
              (∣ q2 , ∣ tri⊎-< (ℝ<->U x<0 , subst (\x -> Real.U x q2) fx-path fxU-q2) ∣ ∣) ∣
        handle2 (tri⊎-> 0<x) = ∥-bind2 handle3 (Real.Inhabited-L fx) (Real.Inhabited-U fx)
          where
          fx : ℝ
          fx = (f⁺ x 0<x)
          handle3 : Σ[ q ∈ ℚ ] (Real.L fx q) -> Σ[ q ∈ ℚ ] (Real.U fx q) -> Ans
          handle3 (q1 , fxL-q1) (q2 , fxU-q2) =
            ∣ (∣ q1 , ∣ tri⊎-> (ℝ<->L 0<x , subst (\x -> Real.L x q1) fx-path fxL-q1) ∣ ∣) ,
              (∣ q2 , ∣ tri⊎-> (ℝ<->L 0<x , subst (\x -> Real.U x q2) fx-path fxU-q2) ∣ ∣) ∣
        handle2 (tri⊎-= d0x<δ) = ∥-bind2 handle3 (Real.Inhabited-L f0) (Real.Inhabited-U f0)
          where
          handle3 : Σ ℚ (Real.L f0) -> Σ ℚ (Real.U f0) -> Ans
          handle3 (q , f0L-q) (r , f0U-r) =
            ∣ (∣ ((q + (- 1#)) + (- 1#) ,
                  ∣ tri⊎-= (q + (- 1#) , q-2<q-1 , (δ , 0<δ) , ℝ<->U d0x<δ ,
                            (\t dU-t -> proj₁ (close' t dU-t))) ∣) ∣) ,
              (∣ ((r + 1#) + 1# ,
                  ∣ tri⊎-= (r + 1# , r+1<r+2 , (δ , 0<δ) , ℝ<->U d0x<δ ,
                            (\t dU-t -> proj₂ (close' t dU-t))) ∣) ∣) ∣
            where
            q-2<q-1 : ((q + (- 1#)) + (- 1#)) < (q + (- 1#))
            q-2<q-1 = trans-<-= (+₁-preserves-< (minus-flips-0< 0<1)) +-right-zero
            r+1<r+2 : (r + 1#) < ((r + 1#) + 1#)
            r+1<r+2 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1)

            close' : (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ ->
                     Real.L (fℚ t) (q + (- 1#)) × Real.U (fℚ t) (r + 1#)
            close' t dU-δ =
              ℝ<->L (trans-=-< ℚ->ℝ-preserves-diff
                      (trans-<-= (+-preserves-< q<f0 -1<d) diff-step)) ,
              ℝ<->U (trans-=-< (sym diff-step)
                      (trans-<-= (+-preserves-< f0<r d<1) (sym ℚ->ℝ-preserves-+)))
              where
              q<f0 : ℚ->ℝ q < f 0∈
              q<f0 = L->ℝ< f0L-q
              -1<d : (- 1#) < diff (f 0∈) (fℚ t)
              -1<d =
                trans-<-≤ (minus-flips-< (close (ℚ->ℝ≤≥0 t) (U->ℝ< dU-δ)))
                  (trans-≤-= (minus-flips-≤ max-≤-right)
                    minus-double-inverse)
              f0<r : f 0∈ < ℚ->ℝ r
              f0<r = U->ℝ< f0U-r
              d<1 : diff (f 0∈) (fℚ t) < 1#
              d<1 = trans-≤-< max-≤-left (close (ℚ->ℝ≤≥0 t) (U->ℝ< dU-δ))

    isLowerSet-L : isLowerSet L
    isLowerSet-L {q} {r} q<r = ∥-map handle
      where
      handle : L' r -> L' q
      handle (tri⊎-< (xU0 , fLr)) = tri⊎-< (xU0 , Real.isLowerSet-L (f _) q<r fLr)
      handle (tri⊎-> (xL0 , fLr)) = tri⊎-> (xL0 , Real.isLowerSet-L (f _) q<r fLr)
      handle (tri⊎-= (r' , r<r' , δ⁺ , dxU-δ , close-L)) =
        tri⊎-= (r , q<r , δ⁺ , dxU-δ ,
                (\t dt<δ -> Real.isLowerSet-L (f _) r<r' (close-L t dt<δ)))

    isUpperSet-U : isUpperSet U
    isUpperSet-U {q} {r} q<r = ∥-map handle
      where
      handle : U' q -> U' r
      handle (tri⊎-< (xU0 , fUr)) = tri⊎-< (xU0 , Real.isUpperSet-U (f _) q<r fUr)
      handle (tri⊎-> (xL0 , fUr)) = tri⊎-> (xL0 , Real.isUpperSet-U (f _) q<r fUr)
      handle (tri⊎-= (q' , q'<q , δ⁺ , dxU-δ , close-U)) =
        tri⊎-= (q , q<r , δ⁺ , dxU-δ ,
                (\t dt<δ -> Real.isUpperSet-U (f _) q'<q (close-U t dt<δ)))


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' q -> ∃[ r ∈ ℚ ] ((q < r) × L r)
      handle (tri⊎-< (xU0 , fxLq)) =
        ∥-map handle2 (Real.isUpperOpen-L (f⁻ x (U->ℝ< xU0)) q fxLq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((q < r) × Real.L (f _) r) -> Σ[ r ∈ ℚ ] ((q < r) × L r)
        handle2 (r , q<r , fUr) = r , q<r , ∣ tri⊎-< (_ , fUr) ∣
      handle (tri⊎-> (xL0 , fxLq)) =
        ∥-map handle2 (Real.isUpperOpen-L (f⁺ x (L->ℝ< xL0)) q fxLq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((q < r) × Real.L (f _) r) -> Σ[ r ∈ ℚ ] ((q < r) × L r)
        handle2 (r , q<r , fLr) = r , q<r , ∣ tri⊎-> (_ , fLr) ∣
      handle (tri⊎-=  (q' , q<q' , δ⁺ , dU-δ , close-L)) =
        ∣ mean q q' , mean-<₁ q<q' ,
          ∣ tri⊎-= (q' , mean-<₂ q<q' , δ⁺ , dU-δ , close-L) ∣ ∣

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-bind handle
      where
      handle : U' q -> ∃[ r ∈ ℚ ] ((r < q) × U r)
      handle (tri⊎-< (xU0 , fxUq)) = ∥-map handle2 (Real.isLowerOpen-U (f _) q fxUq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((r < q) × Real.U (f _) r) -> Σ[ r ∈ ℚ ] ((r < q) × U r)
        handle2 (r , r<q , fUr) = r , r<q , ∣ tri⊎-< (xU0 , fUr) ∣
      handle (tri⊎-> (xL0 , fxUq)) = ∥-map handle2 (Real.isLowerOpen-U (f _) q fxUq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((r < q) × Real.U (f _) r) -> Σ[ r ∈ ℚ ] ((r < q) × U r)
        handle2 (r , r<q , fUr) = r , r<q , ∣ tri⊎-> (xL0 , fUr) ∣
      handle (tri⊎-= (q' , q'<q , δ⁺ , dU-δ , close-U)) =
        ∣ mean q' q , mean-<₂ q'<q ,
          ∣ tri⊎-= (q' , mean-<₁ q'<q , δ⁺ , dU-δ , close-U) ∣ ∣


    ∃closeℚ : (x : ℝ) ((ε , _) : ℝ⁺) -> ∃[ q ∈ ℚ ] (distance x (ℚ->ℝ q) < ε)
    ∃closeℚ x (ε , 0<ε) = ∥-bind handle 0<ε
      where
      handle : 0# ℝ<' ε -> _
      handle (ℝ<'-cons εℚ 0U-εℚ εL-εℚ) = ∥-map handle2 (find-small-ℝ∈Iℚ x (εℚ , U->ℚ< 0U-εℚ))
        where
        handle2 : Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ x qi × i-width qi ≤ εℚ) -> _
        handle2 (Iℚ-cons l u l<u , (xL-l , xU-u) , w≤εℚ) = l , dis-xl<ε
          where
          l<x : ℚ->ℝ l < x
          l<x = L->ℝ< xL-l
          dis-xl=dif-lx : distance x (ℚ->ℝ l) == diff (ℚ->ℝ l) x
          dis-xl=dif-lx = distance-commuteᵉ x (ℚ->ℝ l) >=> abs-0≤-path (weaken-< (diff-0<⁺ l<x))
          0<dif-xu : 0# < diff x (ℚ->ℝ u)
          0<dif-xu = diff-0<⁺ (U->ℝ< xU-u)
          dis-xl<ε : distance x (ℚ->ℝ l) < ε
          dis-xl<ε =
            trans-=-< (dis-xl=dif-lx >=> sym +-right-zero)
              (trans-< (+₁-preserves-< 0<dif-xu)
                (trans-=-< diff-trans
                  (trans-≤-<
                    (trans-=-≤ (sym ℚ->ℝ-preserves-diff) (ℚ->ℝ-preserves-≤ w≤εℚ))
                    (L->ℝ< εL-εℚ))))


    closeℝ-U :
      {δ q q' : ℚ} -> (∀ (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ -> Real.U (fℚ t) q) -> q < q' ->
      (∀ (t∈@(t , _) : ℝ≤≥0) -> Real.U (distance 0# t) δ -> Real.U (f t∈) q')
    closeℝ-U {δ} {q} {q'} close q<q' t∈@(t , _) dtU-δ =
      unsquash (Real.isProp-U (f t∈) q') (∥-bind handle (cf t∈ (ε , 0<ε)))
      where
      ε = ℚ->ℝ (diff q q')
      0<ε = ℚ->ℝ-preserves-< (diff-0<⁺ q<q')
      dt<δ = (U->ℝ< dtU-δ)
      0<δ : 0# < δ
      0<δ = ℚ->ℝ-reflects-< (trans-≤-< abs-0≤ dt<δ)

      handle : (Σ[ (δ1 , _) ∈ ℝ⁺ ] ∀ (x∈@(x , _) : ℝ≤≥0) ->
                  distance t x < δ1 -> distance (f t∈) (f x∈) < ε) ->
               ∥ Real.U (f t∈) q' ∥
      handle ((δ1 , 0<δ1) , close-t) = ∥-map handle2 (∃closeℚ t (δ' , 0<δ'))
        where
        δ2 = diff (distance 0# t) (ℚ->ℝ δ)
        0<δ2 = diff-0<⁺ dt<δ
        δ' : ℝ
        δ' = min δ1 δ2
        0<δ' : 0# < δ'
        0<δ' = min-greatest-< 0<δ1 0<δ2

        handle2 : (Σ[ x ∈ ℚ ] (distance t (ℚ->ℝ x) < δ')) -> Real.U (f t∈) q'
        handle2 (x , tx<δ') = ℝ<->U ft<q'
          where
          x∈ = ℚ->ℝ≤≥0 x
          tx<δ1 = trans-<-≤ tx<δ' min-≤-left
          tx<δ2 = trans-<-≤ tx<δ' min-≤-right

          d0x<δ : distance 0# (ℚ->ℝ x) < (ℚ->ℝ δ)
          d0x<δ = trans-≤-< (distance-triangleᵉ 0# _ (ℚ->ℝ x))
                            (trans-<-= (+₁-preserves-< tx<δ2) diff-step)

          fx<q : (f x∈) < ℚ->ℝ q
          fx<q = U->ℝ< (close x (ℝ<->U d0x<δ))

          dfxft<ε : diff (f x∈) (f t∈) < ε
          dfxft<ε = trans-≤-< (trans-≤-= max-≤-left (distance-commuteᵉ (f x∈) (f t∈)))
                              (close-t x∈ tx<δ1)

          ft<q' : (f t∈) < ℚ->ℝ q'
          ft<q' =
            (trans-=-< (sym diff-step)
              (trans-<-= (+-preserves-< fx<q dfxft<ε)
                (+-right ℚ->ℝ-preserves-diff >=> diff-step)))

    closeℝ-L :
      {δ q q' : ℚ} -> (∀ (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ -> Real.L (fℚ t) q) -> q' < q ->
      (∀ (t∈@(t , _) : ℝ≤≥0) -> Real.U (distance 0# t) δ -> Real.L (f t∈) q')
    closeℝ-L {δ} {q} {q'} close q'<q t∈@(t , _) dtU-δ =
      unsquash (Real.isProp-L (f t∈) q') (∥-bind handle (cf t∈ (ε , 0<ε)))
      where
      ε = ℚ->ℝ (diff q' q)
      0<ε = ℚ->ℝ-preserves-< (diff-0<⁺ q'<q)
      dt<δ = (U->ℝ< dtU-δ)
      0<δ : 0# < δ
      0<δ = ℚ->ℝ-reflects-< (trans-≤-< abs-0≤ dt<δ)

      handle : (Σ[ (δ1 , _) ∈ ℝ⁺ ] ∀ (x∈@(x , _) : ℝ≤≥0) ->
                  distance t x < δ1 -> distance (f t∈) (f x∈) < ε) ->
               ∥ Real.L (f t∈) q' ∥
      handle ((δ1 , 0<δ1) , close-t) = ∥-map handle2 (∃closeℚ t (δ' , 0<δ'))
        where
        δ2 = diff (distance 0# t) (ℚ->ℝ δ)
        0<δ2 = diff-0<⁺ dt<δ
        δ' : ℝ
        δ' = min δ1 δ2
        0<δ' : 0# < δ'
        0<δ' = min-greatest-< 0<δ1 0<δ2

        handle2 : (Σ[ x ∈ ℚ ] (distance t (ℚ->ℝ x) < δ')) -> Real.L (f t∈) q'
        handle2 (x , tx<δ') = ℝ<->L q'<ft
          where
          x∈ = ℚ->ℝ≤≥0 x
          tx<δ1 = trans-<-≤ tx<δ' min-≤-left
          tx<δ2 = trans-<-≤ tx<δ' min-≤-right

          d0x<δ : distance 0# (ℚ->ℝ x) < (ℚ->ℝ δ)
          d0x<δ = trans-≤-< (distance-triangleᵉ 0# _ (ℚ->ℝ x))
                            (trans-<-= (+₁-preserves-< tx<δ2) diff-step)

          q<fx : ℚ->ℝ q < (f x∈)
          q<fx = L->ℝ< (close x (ℝ<->U d0x<δ))

          dftfx<ε : diff (f t∈) (f x∈) < ε
          dftfx<ε = trans-≤-< max-≤-left
                              (close-t x∈ tx<δ1)

          -ε<dfxft : (- ε) < diff (f x∈) (f t∈)
          -ε<dfxft = trans-<-= (minus-flips-< dftfx<ε) (sym diff-anticommute)

          q'<ft : ℚ->ℝ q' < f t∈
          q'<ft =
            (trans-=-< (sym diff-step >=> +-right (diff-anticommute >=>
                                                   cong -_ (sym ℚ->ℝ-preserves-diff)))
              (trans-<-= (+-preserves-< q<fx -ε<dfxft)
                 diff-step))


    disjoint : Universal (Comp (L ∩ U))
    disjoint q (Lq , Uq) = unsquash isPropBot (∥-map2 handle Lq Uq)
      where
      handle : L' q -> U' q -> Bot
      handle (tri⊎-> (_ , fxLq)) (tri⊎-> (_ , fxUq)) =
        Real.disjoint (f _) q (subst (\fx -> Real.L fx q) fx-path fxLq , fxUq)
      handle (tri⊎-< (_ , fxLq)) (tri⊎-< (_ , fxUq)) =
        Real.disjoint (f _) q (subst (\fx -> Real.L fx q) fx-path fxLq , fxUq)
      handle (tri⊎-< (xU0 , _)) (tri⊎-> (xL0 , _)) =
        Real.disjoint x 0# (xL0 , xU0)
      handle (tri⊎-> (xL0 , _)) (tri⊎-< (xU0 , _)) =
        Real.disjoint x 0# (xL0 , xU0)
      handle (tri⊎-> (xL0 , fxLq)) (tri⊎-= (q' , q'<q , δ⁺ , dU-δ , close)) =
        unsquash isPropBot (∥-map handle2 (Real.isUpperOpen-L fx q fxLq))
        where
        fx = f⁺ x (L->ℝ< xL0)
        handle2 : Σ[ r ∈ ℚ ] (q < r × Real.L fx r) -> Bot
        handle2 (r , q<r , fxLr) = Real.disjoint fx r (fxLr , fxUr)
          where
          fxUr : Real.U fx r
          fxUr = closeℝ-U close (trans-< q'<q q<r) _ dU-δ
      handle (tri⊎-< (xU0 , fxLq)) (tri⊎-= (q' , q'<q , δ⁺ , dU-δ , close)) =
        unsquash isPropBot (∥-map handle2 (Real.isUpperOpen-L fx q fxLq))
        where
        fx = f⁻ x (U->ℝ< xU0)
        handle2 : Σ[ r ∈ ℚ ] (q < r × Real.L fx r) -> Bot
        handle2 (r , q<r , fxLr) = Real.disjoint fx r (fxLr , fxUr)
          where
          fxUr : Real.U fx r
          fxUr = closeℝ-U close (trans-< q'<q q<r) _ dU-δ
      handle (tri⊎-= (q' , q<q' , δ⁺ , dU-δ , close)) (tri⊎-> (xL0 , fxUq))  =
        unsquash isPropBot (∥-map handle2 (Real.isLowerOpen-U fx q fxUq))
        where
        fx = f⁺ x (L->ℝ< xL0)
        handle2 : Σ[ r ∈ ℚ ] (r < q × Real.U fx r) -> Bot
        handle2 (r , r<q , fxUr) = Real.disjoint fx r (fxLr , fxUr)
          where
          fxLr : Real.L fx r
          fxLr = closeℝ-L close (trans-< r<q q<q') _ dU-δ
      handle (tri⊎-= (q' , q<q' , δ⁺ , dU-δ , close)) (tri⊎-< (xU0 , fxUq))  =
        unsquash isPropBot (∥-map handle2 (Real.isLowerOpen-U fx q fxUq))
        where
        fx = f⁻ x (U->ℝ< xU0)
        handle2 : Σ[ r ∈ ℚ ] (r < q × Real.U fx r) -> Bot
        handle2 (r , r<q , fxUr) = Real.disjoint fx r (fxLr , fxUr)
          where
          fxLr : Real.L fx r
          fxLr = closeℝ-L close (trans-< r<q q<q') _ dU-δ
      handle (tri⊎-= (q1 , q<q1 , (δ1 , 0<δ1) , dU-δ1 , close1))
             (tri⊎-= (q2 , q2<q , (δ2 , 0<δ2) , dU-δ2 , close2)) = asym-< q<f0 f0<q
        where
        0=0 : Path ℝ 0# 0#
        0=0 = refl
        q<f0 : ℚ->ℝ q < fℚ 0#
        q<f0 = trans-< (ℚ->ℝ-preserves-< q<q1)
                       (L->ℝ< (close1 0# (ℝ<->U (trans-=-< (path->zero-distance 0=0)
                                                           (ℚ->ℝ-preserves-< 0<δ1)))))
        f0<q : fℚ 0# < ℚ->ℝ q
        f0<q = trans-< (U->ℝ< (close2 0# (ℝ<->U (trans-=-< (path->zero-distance 0=0)
                                                           (ℚ->ℝ-preserves-< 0<δ2)))))
                       (ℚ->ℝ-preserves-< q2<q)

    located⁺ : x.L 0# -> (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located⁺ xL0 q r q<r = ∥-map handle (fx.located q r q<r)
      where
      fx = (f⁺ x (L->ℝ< xL0))
      module fx = Real fx
      handle : fx.L q ⊎ fx.U r -> L q ⊎ U r
      handle (inj-l fxLq) = inj-l ∣ tri⊎-> (xL0 , fxLq) ∣
      handle (inj-r fxUr) = inj-r ∣ tri⊎-> (xL0 , fxUr) ∣


    located⁻ : x.U 0# -> (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located⁻ xU0 q r q<r = ∥-map handle (fx.located q r q<r)
      where
      fx = (f⁻ x (U->ℝ< xU0))
      module fx = Real fx
      handle : fx.L q ⊎ fx.U r -> L q ⊎ U r
      handle (inj-l fxLq) = inj-l ∣ tri⊎-< (xU0 , fxLq) ∣
      handle (inj-r fxUr) = inj-r ∣ tri⊎-< (xU0 , fxUr) ∣


    located : (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located q r q<r = ∥-bind handle (Real.located f0 q' r' q'<r')
      where
      q' = mean q (mean q r)
      r' = mean (mean q r) r
      q<q' : q < q'
      q<q' = mean-<₁ (mean-<₁ q<r)
      r'<r : r' < r
      r'<r = mean-<₂ (mean-<₂ q<r)
      q'<r' : q' < r'
      q'<r' = trans-< (mean-<₂ (mean-<₁ q<r)) (mean-<₁ (mean-<₂ q<r))

      Ans = ∥ L q ⊎ U r ∥
      handle : (f0.L q' ⊎ f0.U r') -> Ans
      handle (inj-l f0Lq') = ∥-bind handle2 (isContinuous-lower-bound cont-f 0∈ q'<f0)
        where
        q'<f0 = L->ℝ< f0Lq'
        handle2 : (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ℝ≤≥0) ->
                                       distance 0# y < δ -> ℚ->ℝ q' < f y∈) -> Ans
        handle2 (δ1⁺@(δ1 , 0<δ1) , δ1-close) = ∥-bind handle3 0<δ1
          where
          handle3 : 0# ℝ<' δ1 -> Ans
          handle3 (ℝ<'-cons δ2 0U-δ2 δ1L-δ2) =
            ∥-bind handle4 (split-distance<ε 0# x (ℚ->ℝ δ2 , U->ℝ< 0U-δ2))
            where
            handle4 : Tri⊎ (x < 0#) (distance 0# x < (ℚ->ℝ δ2)) (0# < x) -> Ans
            handle4 (tri⊎-< x<0)   = located⁻ (ℝ<->U x<0) q r q<r
            handle4 (tri⊎-> 0<x)   = located⁺ (ℝ<->L 0<x) q r q<r
            handle4 (tri⊎-= d0x<δ2) =
              ∣ inj-l (∣ tri⊎-= (q' , q<q' , (δ2 , U->ℚ< 0U-δ2) , ℝ<->U d0x<δ2 , δ2-close ) ∣) ∣
              where
              δ2-close : (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ2 -> Real.L (fℚ t) q'
              δ2-close t d0tU-δ2 =
                ℝ<->L (δ1-close (ℚ->ℝ≤≥0 t) (trans-< (U->ℝ< d0tU-δ2) (L->ℝ< δ1L-δ2)))
      handle (inj-r f0Ur') = ∥-bind handle2 (isContinuous-upper-bound cont-f 0∈ f0<r')
        where
        f0<r' = U->ℝ< f0Ur'
        handle2 : (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ℝ≤≥0) ->
                                       distance 0# y < δ -> f y∈ < ℚ->ℝ r') -> Ans
        handle2 (δ1⁺@(δ1 , 0<δ1) , δ1-close) = ∥-bind handle3 0<δ1
          where
          handle3 : 0# ℝ<' δ1 -> Ans
          handle3 (ℝ<'-cons δ2 0U-δ2 δ1L-δ2) =
            ∥-bind handle4 (split-distance<ε 0# x (ℚ->ℝ δ2 , U->ℝ< 0U-δ2))
            where
            handle4 : Tri⊎ (x < 0#) (distance 0# x < (ℚ->ℝ δ2)) (0# < x) -> Ans
            handle4 (tri⊎-< x<0)   = located⁻ (ℝ<->U x<0) q r q<r
            handle4 (tri⊎-> 0<x)   = located⁺ (ℝ<->L 0<x) q r q<r
            handle4 (tri⊎-= d0x<δ2) =
              ∣ inj-r (∣ tri⊎-= (r' , r'<r , (δ2 , U->ℚ< 0U-δ2) , ℝ<->U d0x<δ2 , δ2-close ) ∣) ∣
              where
              δ2-close : (t : ℚ) -> Real.U (distance 0# (ℚ->ℝ t)) δ2 -> Real.U (fℚ t) r'
              δ2-close t d0tU-δ2 =
                ℝ<->U (δ1-close (ℚ->ℝ≤≥0 t) (trans-< (U->ℝ< d0tU-δ2) (L->ℝ< δ1L-δ2)))

  opaque
    extend-≤≥0 : ℝ
    extend-≤≥0 = record
      { L = L
      ; U = U
      ; isProp-L = \_ -> squash
      ; isProp-U = \_ -> squash
      ; Inhabited-L = proj₁ Inhabited-LU
      ; Inhabited-U = proj₂ Inhabited-LU
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; disjoint = disjoint
      ; located = located
      }
