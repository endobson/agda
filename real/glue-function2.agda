{-# OPTIONS --cubical --safe --exact-split #-}

module real.glue-function2 where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import funext
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import hlevel
open import nat
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-field.mean
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.open-interval
open import rational.order
open import real
open import real.apartness
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.rational
open import real.continuous.bounds
open import real.derivative3
open import real.derivative3.slope
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.open-interval
open import real.order
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import truncation

ℝ≤≥0 : Type₁
ℝ≤≥0 = Σ[ x ∈ ℝ ] ∥ (x ≤ 0#) ⊎ (0# ≤ x) ∥

ℝ≤≥0S : Subtype ℝ ℓ-one
ℝ≤≥0S x =  ∥ (x ≤ 0#) ⊎ (0# ≤ x) ∥ , squash

private
  0∈ : ∈-Subtype ℝ≤≥0S
  0∈ = 0# , ∣ inj-l refl-≤ ∣


{-
module _ (f : (x : ℝ≤≥0) -> ℝ) (cont-f : isContinuous ℝ≤≥0S f) (x : ℝ) (magic : Magic) where
  private
    module x = Real x
    contℚ-f = isContinuous->isContinuousℚ ℝ≤≥0S cont-f

    ℚ->ℝ≤≥0 : ℚ -> ℝ≤≥0
    ℚ->ℝ≤≥0 q = ℚ->ℝ q , case (split-< 0# q) of
      \{ (inj-l 0<q) -> ∣ inj-r (ℚ->ℝ-preserves-≤ (weaken-< 0<q)) ∣
       ; (inj-r q≤0) -> ∣ inj-l (ℚ->ℝ-preserves-≤ q≤0) ∣
       }

    fℚ : ℚ -> ℝ
    fℚ q = f (ℚ->ℝ≤≥0 q)

    f⁺ : (x : ℝ) -> 0# < x -> ℝ
    f⁺ x 0<x = f (x , ∣ inj-r (weaken-< 0<x) ∣)
    f⁻ : (x : ℝ) -> x < 0# -> ℝ
    f⁻ x x<0 = f (x , ∣ inj-l (weaken-< x<0) ∣)

    L'0< : Pred ℚ ℓ-zero
    L'0< q = Σ[ xL ∈ x.L 0# ] (Real.L (f⁺ x (L->ℝ< xL)) q)

    L'<0 : Pred ℚ ℓ-zero
    L'<0 q = Σ[ xU ∈ x.U 0# ] (Real.L (f⁻ x (U->ℝ< xU)) q)

    L'ε : Pred ℚ ℓ-zero
    L'ε q = Σ[ (r , _) ∈ ℚ⁻ ] Σ[ (s , _) ∈ ℚ⁺ ] Σ[ q' ∈ ℚ ]
              (x.L r × x.U s × (q < q') × ∀ t -> r < t -> t < s -> Real.L (fℚ t) q')

    L : Pred ℚ ℓ-zero
    L q = ∥ (L'0< q ⊎ L'<0 q) ⊎ L'ε q ∥

    U'0< : Pred ℚ ℓ-zero
    U'0< q = Σ[ xL ∈ x.L 0# ] (Real.U (f⁺ x (L->ℝ< xL)) q)

    U'<0 : Pred ℚ ℓ-zero
    U'<0 q = Σ[ xU ∈ x.U 0# ] (Real.U (f⁻ x (U->ℝ< xU)) q)

    U'ε : Pred ℚ ℓ-zero
    U'ε q = Σ[ (r , _) ∈ ℚ⁻ ] Σ[ (s , _) ∈ ℚ⁺ ] Σ[ q' ∈ ℚ ]
              (x.L r × x.U s × q' < q × ∀ t -> r < t -> t < s -> Real.U (fℚ t) q')

    U : Pred ℚ ℓ-zero
    U q = ∥ (U'0< q ⊎ U'<0 q) ⊎ U'ε q ∥

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
          dis-xl=dif-lx = distance-commute >=> abs-0≤-path (weaken-< (diff-0<⁺ l<x))
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


    fx-path : {p1 p2 : ∥ (x ≤ 0#) ⊎ (0# ≤ x) ∥} -> f (x , p1) == f (x , p2)
    fx-path = cong f (ΣProp-path squash refl)

    closeℝ-U : {q q' r s : ℚ} -> (∀ (t : ℚ) -> r < t -> t < s -> Real.U (fℚ t) q) -> q < q' ->
               (∀ (t∈@(t , _) : ℝ≤≥0) -> Real.L t r -> Real.U t s -> Real.U (f t∈) q')
    closeℝ-U {q} {q'} {r} {s} close q<q' t∈@(t , _) tL-r tU-s =
      unsquash (Real.isProp-U (f t∈) q') (∥-bind handle (cont-f t∈ (ε , 0<ε)))
      where
      ε = ℚ->ℝ (diff q q')
      0<ε = ℚ->ℝ-preserves-< (diff-0<⁺ q<q')

      handle : (Σ[ (δ1 , _) ∈ ℝ⁺ ] ∀ (x∈@(x , _) : ℝ≤≥0) ->
                  distance t x < δ1 -> distance (f t∈) (f x∈) < ε) ->
               ∥ Real.U (f t∈) q' ∥
      handle ((δ1 , 0<δ1) , close-t) = ∥-map handle2 (∃closeℚ t (δ , 0<δ))
        where
        r<t : ℚ->ℝ r < t
        r<t = L->ℝ< tL-r
        t<s : t < ℚ->ℝ s
        t<s = U->ℝ< tU-s
        δ2 = diff (ℚ->ℝ r) t
        δ3 = diff t (ℚ->ℝ s)
        0<δ2 = diff-0<⁺ r<t
        0<δ3 = diff-0<⁺ t<s

        δ = min δ1 (min δ2 δ3)
        0<δ = min-greatest-< 0<δ1 (min-greatest-< 0<δ2 0<δ3)

        handle2 : (Σ[ x ∈ ℚ ] (distance t (ℚ->ℝ x) < δ)) -> Real.U (f t∈) q'
        handle2 (x , tx<δ) = ℝ<->U ft<q'
          where
          tx<δ1 = trans-<-≤ tx<δ min-≤-left
          tx<δ2 = trans-<-≤ tx<δ (trans-≤ min-≤-right min-≤-left)
          tx<δ3 = trans-<-≤ tx<δ (trans-≤ min-≤-right min-≤-right)
          x∈ = ℚ->ℝ≤≥0 x
          r<x : r < x
          r<x = ℚ->ℝ-reflects-< (distance-diff-< (trans-=-< distance-commute tx<δ2))
          x<s : x < s
          x<s = ℚ->ℝ-reflects-< (distance-diff-<' tx<δ3)

          dftfx<ε : distance (f t∈) (f x∈) < ε
          dftfx<ε = close-t x∈ tx<δ1
          fx<q : (f x∈) < ℚ->ℝ q
          fx<q = U->ℝ< (close x r<x x<s)
          ft<q' : (f t∈) < ℚ->ℝ q'
          ft<q' =
            (trans-≤-< (trans-=-≤ (sym diff-step) (trans-≤-= (+₁-preserves-≤ max-≤-left)
                                                             (+-right distance-commute)))
              (trans-<-= (+-preserves-< fx<q dftfx<ε)
                (+-right ℚ->ℝ-preserves-diff >=> diff-step)))

    closeℝ-L : {q q' r s : ℚ} -> (∀ (t : ℚ) -> r < t -> t < s -> Real.L (fℚ t) q) -> q' < q ->
               (∀ (t∈@(t , _) : ℝ≤≥0) -> Real.L t r -> Real.U t s -> Real.L (f t∈) q')
    closeℝ-L {q} {q'} {r} {s} close q'<q t∈@(t , _) tL-r tU-s =
      unsquash (Real.isProp-L (f t∈) q') (∥-bind handle (cont-f t∈ (ε , 0<ε)))
      where
      ε = ℚ->ℝ (diff q' q)
      0<ε = ℚ->ℝ-preserves-< (diff-0<⁺ q'<q)

      handle : (Σ[ (δ1 , _) ∈ ℝ⁺ ] ∀ (x∈@(x , _) : ℝ≤≥0) ->
                  distance t x < δ1 -> distance (f t∈) (f x∈) < ε) ->
               ∥ Real.L (f t∈) q' ∥
      handle ((δ1 , 0<δ1) , close-t) = ∥-map handle2 (∃closeℚ t (δ , 0<δ))
        where
        r<t : ℚ->ℝ r < t
        r<t = L->ℝ< tL-r
        t<s : t < ℚ->ℝ s
        t<s = U->ℝ< tU-s
        δ2 = diff (ℚ->ℝ r) t
        δ3 = diff t (ℚ->ℝ s)
        0<δ2 = diff-0<⁺ r<t
        0<δ3 = diff-0<⁺ t<s

        δ = min δ1 (min δ2 δ3)
        0<δ = min-greatest-< 0<δ1 (min-greatest-< 0<δ2 0<δ3)

        handle2 : (Σ[ x ∈ ℚ ] (distance t (ℚ->ℝ x) < δ)) -> Real.L (f t∈) q'
        handle2 (x , tx<δ) = ℝ<->L q'<ft
          where
          tx<δ1 = trans-<-≤ tx<δ min-≤-left
          tx<δ2 = trans-<-≤ tx<δ (trans-≤ min-≤-right min-≤-left)
          tx<δ3 = trans-<-≤ tx<δ (trans-≤ min-≤-right min-≤-right)
          x∈ = ℚ->ℝ≤≥0 x
          r<x : r < x
          r<x = ℚ->ℝ-reflects-< (distance-diff-< (trans-=-< distance-commute tx<δ2))
          x<s : x < s
          x<s = ℚ->ℝ-reflects-< (distance-diff-<' tx<δ3)

          dis-ftfx<ε : distance (f t∈) (f x∈) < ε
          dis-ftfx<ε = close-t x∈ tx<δ1
          dif-ftfx<dq : diff (f t∈) (f x∈) < ℚ->ℝ (diff q' q)
          dif-ftfx<dq = trans-≤-< max-≤-left dis-ftfx<ε
          dq<dif-fxft : ℚ->ℝ (diff q q') < (diff (f x∈) (f t∈))
          dq<dif-fxft =
            trans-=-< (cong ℚ->ℝ diff-anticommute >=> ℚ->ℝ-preserves--)
              (trans-<-= (minus-flips-< dif-ftfx<dq)
                (sym diff-anticommute))

          q<fx : ℚ->ℝ q < (f x∈)
          q<fx = L->ℝ< (close x r<x x<s)
          q'<ft : ℚ->ℝ q' < (f t∈)
          q'<ft =
            (trans-=-< (cong ℚ->ℝ (sym diff-step) >=> ℚ->ℝ-preserves-+)
              (trans-<-= (+-preserves-< q<fx dq<dif-fxft)
                diff-step))



    Inhabited-L : Inhabited L
    Inhabited-L = ∥-bind handle (cont-f 0∈ (1# , 0<1))
      where
      handle : Σ[ (δ , _) ∈ ℝ⁺ ] (∀ y∈ -> distance 0# _ < δ -> distance (f 0∈) (f y∈) < 1#) ->
               Inhabited L
      handle ((δ1 , 0<δ1) , close) = ∥-bind handle-0<δ1 0<δ1
        where
        handle-0<δ1 : 0# ℝ<' δ1 -> Inhabited L
        handle-0<δ1 (ℝ<'-cons δℚ 0U-δℚ δ1L-δℚ) =
          ∥-bind2 handle2 (comparison-< (- δ) x 0# (minus-flips-0< 0<δ))
                          (comparison-< 0# x δ 0<δ)
          where
          δ = ℚ->ℝ δℚ
          0<δℚ = U->ℚ< 0U-δℚ
          0<δ = U->ℝ< 0U-δℚ
          δ<δ1 = L->ℝ< δ1L-δℚ

          handle2 : ((- δ) < x) ⊎ (x < 0#) -> (0# < x) ⊎ (x < δ) -> Inhabited L
          handle2 (inj-r x<0) _ = ∥-map handle3 (Real.Inhabited-L (f⁻ x x<0))
            where
            handle3 : Σ[ q ∈ ℚ ] (Real.L (f⁻ x x<0) q) -> Σ ℚ L
            handle3 (q , fxL-q) = q , ∣ inj-l (inj-r (ℝ<->U x<0 , subst (\x -> Real.L x q) path fxL-q)) ∣
              where
              path : f⁻ x _ == f⁻ x _
              path = cong (f⁻ x) (isProp-< _ _)
          handle2 (inj-l -δ<x) (inj-l 0<x) = ∥-map handle3 (Real.Inhabited-L (f⁺ x 0<x))
            where
            handle3 : Σ[ q ∈ ℚ ] (Real.L (f⁺ x 0<x) q) -> Σ ℚ L
            handle3 (q , fxL-q) = q , ∣ inj-l (inj-l (ℝ<->L 0<x , subst (\x -> Real.L x q) path fxL-q)) ∣
              where
              path : f⁺ x _ == f⁺ x _
              path = cong (f⁺ x) (isProp-< _ _)
          handle2 (inj-l -δ<x) (inj-r x<δ) = ∥-map handle4 (Real.Inhabited-L (f 0∈))
            where
            handle4 : Σ[ q ∈ ℚ ] (Real.L (f 0∈) q) -> Σ ℚ L
            handle4 (q , f0L-q) = (q + (- 1#)) + (- 1#) ,
              ∣ inj-r ((- δℚ , (minus-flips-0< 0<δℚ)) , (δℚ , 0<δℚ) , q + (- 1#) ,
                       ℝ<->L (trans-=-< ℚ->ℝ-preserves-- -δ<x) ,
                       ℝ<->U x<δ ,
                       q-2<q-1 ,
                       closeℚ) ∣
              where
              q-2<q-1 : ((q + (- 1#)) + (- 1#)) < (q + (- 1#))
              q-2<q-1 = trans-<-= (+₁-preserves-< (minus-flips-0< 0<1)) +-right-zero


              closeℚ : (t : ℚ) -> (- δℚ) < t -> t < δℚ -> Real.L (fℚ t) (q + (- 1#))
              closeℚ t -δℚ<t t<δℚ = ℝ<->L q-1<ft
                where
                q<f0 : ℚ->ℝ q < f 0∈
                q<f0 = L->ℝ< f0L-q

                dis-0t<δ1 : distance 0# (ℚ->ℝ t) < δ1
                dis-0t<δ1 =
                  trans-< (max-least-< 0t<δ (trans-=-< (sym diff-anticommute) t0<δ))
                          δ<δ1
                  where
                  t<δ : ℚ->ℝ t < δ
                  t<δ = ℚ->ℝ-preserves-< t<δℚ
                  -δ<t : (- δ) < ℚ->ℝ t
                  -δ<t = trans-=-< (sym ℚ->ℝ-preserves--) (ℚ->ℝ-preserves-< -δℚ<t)
                  0t<δ : diff 0# (ℚ->ℝ t) < δ
                  0t<δ = trans-=-< (sym +-left-zero >=> diff-step) t<δ
                  t0<δ : diff (ℚ->ℝ t) 0# < δ
                  t0<δ = trans-<-= (trans-=-< +-left-zero (minus-flips-< -δ<t))
                                   minus-double-inverse


                dis-f0t<1 : distance (f 0∈) (fℚ t) < 1#
                dis-f0t<1 = close _ dis-0t<δ1

                -1<dif-f0t : (- 1#) < diff (f 0∈) (fℚ t)
                -1<dif-f0t =
                  trans-<-= (minus-flips-< (trans-≤-< (trans-=-≤ diff-anticommute max-≤-right)
                                                      dis-f0t<1))
                    (sym diff-anticommute)

                q-1<ft : ℚ->ℝ (q + (- 1#)) < (fℚ t)
                q-1<ft =
                  trans-=-< ℚ->ℝ-preserves-diff
                    (trans-<-= (+-preserves-< q<f0 -1<dif-f0t)
                      diff-step)


    Inhabited-U : Inhabited U
    Inhabited-U = ∥-bind handle (cont-f 0∈ (1# , 0<1))
      where
      handle : Σ[ (δ , _) ∈ ℝ⁺ ] (∀ y∈ -> distance 0# _ < δ -> distance (f 0∈) (f y∈) < 1#) ->
               Inhabited U
      handle ((δ1 , 0<δ1) , close) = ∥-bind handle-0<δ1 0<δ1
        where
        handle-0<δ1 : 0# ℝ<' δ1 -> Inhabited U
        handle-0<δ1 (ℝ<'-cons δℚ 0U-δℚ δ1L-δℚ) =
          ∥-bind2 handle2 (comparison-< (- δ) x 0# (minus-flips-0< 0<δ))
                          (comparison-< 0# x δ 0<δ)
          where
          δ = ℚ->ℝ δℚ
          0<δℚ = U->ℚ< 0U-δℚ
          0<δ = U->ℝ< 0U-δℚ
          δ<δ1 = L->ℝ< δ1L-δℚ

          handle2 : ((- δ) < x) ⊎ (x < 0#) -> (0# < x) ⊎ (x < δ) -> Inhabited U
          handle2 (inj-r x<0) _ = ∥-map handle3 (Real.Inhabited-U (f⁻ x x<0))
            where
            handle3 : Σ[ q ∈ ℚ ] (Real.U (f⁻ x x<0) q) -> Σ ℚ U
            handle3 (q , fxU-q) = q , ∣ inj-l (inj-r (ℝ<->U x<0 , subst (\x -> Real.U x q) path fxU-q)) ∣
              where
              path : f⁻ x _ == f⁻ x _
              path = cong (f⁻ x) (isProp-< _ _)
          handle2 (inj-l -δ<x) (inj-l 0<x) = ∥-map handle3 (Real.Inhabited-U (f⁺ x 0<x))
            where
            handle3 : Σ[ q ∈ ℚ ] (Real.U (f⁺ x 0<x) q) -> Σ ℚ U
            handle3 (q , fxU-q) = q , ∣ inj-l (inj-l (ℝ<->L 0<x , subst (\x -> Real.U x q) path fxU-q)) ∣
              where
              path : f⁺ x _ == f⁺ x _
              path = cong (f⁺ x) (isProp-< _ _)
          handle2 (inj-l -δ<x) (inj-r x<δ) = ∥-map handle4 (Real.Inhabited-U (f 0∈))
            where
            handle4 : Σ[ q ∈ ℚ ] (Real.U (f 0∈) q) -> Σ ℚ U
            handle4 (q , f0U-q) = (q + 1#) + 1# ,
              ∣ inj-r ((- δℚ , (minus-flips-0< 0<δℚ)) , (δℚ , 0<δℚ) , q + 1# ,
                       ℝ<->L (trans-=-< ℚ->ℝ-preserves-- -δ<x) ,
                       ℝ<->U x<δ ,
                       q+1<q+2 ,
                       closeℚ) ∣
              where
              q+1<q+2 : (q + 1#) < ((q + 1#) + 1#)
              q+1<q+2 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1)

              closeℚ : (t : ℚ) -> (- δℚ) < t -> t < δℚ -> Real.U (fℚ t) (q + 1#)
              closeℚ t -δℚ<t t<δℚ = ℝ<->U ft<q+1
                where
                f0<q : f 0∈ < ℚ->ℝ q
                f0<q = U->ℝ< f0U-q

                dis-0t<δ1 : distance 0# (ℚ->ℝ t) < δ1
                dis-0t<δ1 =
                  trans-< (max-least-< 0t<δ (trans-=-< (sym diff-anticommute) t0<δ))
                          δ<δ1
                  where
                  t<δ : ℚ->ℝ t < δ
                  t<δ = ℚ->ℝ-preserves-< t<δℚ
                  -δ<t : (- δ) < ℚ->ℝ t
                  -δ<t = trans-=-< (sym ℚ->ℝ-preserves--) (ℚ->ℝ-preserves-< -δℚ<t)
                  0t<δ : diff 0# (ℚ->ℝ t) < δ
                  0t<δ = trans-=-< (sym +-left-zero >=> diff-step) t<δ
                  t0<δ : diff (ℚ->ℝ t) 0# < δ
                  t0<δ = trans-<-= (trans-=-< +-left-zero (minus-flips-< -δ<t))
                                   minus-double-inverse


                dis-f0t<1 : distance (f 0∈) (fℚ t) < 1#
                dis-f0t<1 = close _ dis-0t<δ1

                dif-f0t<1 : diff (f 0∈) (fℚ t) < 1#
                dif-f0t<1 = trans-≤-< max-≤-left (close _ dis-0t<δ1)

                ft<q+1 : (fℚ t) < ℚ->ℝ (q + 1#)
                ft<q+1 =
                  trans-=-< (sym diff-step)
                    (trans-<-= (+-preserves-< f0<q dif-f0t<1)
                      (sym ℚ->ℝ-preserves-+))





    isLowerSet-L : isLowerSet L
    isLowerSet-L {q} {r} q<r = ∥-map handle
      where
      handle : (L'0< r ⊎ L'<0 r) ⊎ L'ε r -> (L'0< q ⊎ L'<0 q) ⊎ L'ε q
      handle (inj-l (inj-l (xL0 , fLr))) = inj-l (inj-l (xL0 , Real.isLowerSet-L (f _) q<r fLr))
      handle (inj-l (inj-r (xU0 , fLr))) = inj-l (inj-r (xU0 , Real.isLowerSet-L (f _) q<r fLr))
      handle (inj-r (s , t , r' , xLs , xUt , r<r' , close-L)) =
        inj-r (s , t , r , xLs , xUt , q<r ,
                 (\y s<y y<t -> Real.isLowerSet-L (f _) r<r' (close-L y s<y y<t)))


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : ((L'0< q ⊎ L'<0 q) ⊎ L'ε q) -> ∃[ r ∈ ℚ ] ((q < r) × L r)
      handle (inj-l (inj-l (xL0 , fxLq))) =
        ∥-map handle2 (Real.isUpperOpen-L (f⁺ x (L->ℝ< xL0)) q fxLq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((q < r) × Real.L (f _) r) -> Σ[ r ∈ ℚ ] ((q < r) × L r)
        handle2 (r , q<r , fLr) = r , q<r , ∣ inj-l (inj-l (_ , fLr)) ∣
      handle (inj-l (inj-r (xU0 , fxLq))) =
        ∥-map handle2 (Real.isUpperOpen-L (f⁻ x (U->ℝ< xU0)) q fxLq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((q < r) × Real.L (f _) r) -> Σ[ r ∈ ℚ ] ((q < r) × L r)
        handle2 (r , q<r , fUr) = r , q<r , ∣ inj-l (inj-r (_ , fUr)) ∣
      handle (inj-r ((s , s<0) , (t , 0<t) , q' , xLs , xUt , q<q' , close-L)) =
        ∣ mean q q' , mean-<₁ q<q' ,
          ∣ inj-r ((s , s<0) , (t , 0<t) , q' , xLs , xUt , mean-<₂ q<q' , close-L) ∣ ∣


    isUpperSet-U : isUpperSet U
    isUpperSet-U {q} {r} q<r = ∥-map handle
      where
      handle : (U'0< q ⊎ U'<0 q) ⊎ U'ε q -> (U'0< r ⊎ U'<0 r) ⊎ U'ε r
      handle (inj-l (inj-l (xL0 , fUr))) = inj-l (inj-l (xL0 , Real.isUpperSet-U (f _) q<r fUr))
      handle (inj-l (inj-r (xU0 , fUr))) = inj-l (inj-r (xU0 , Real.isUpperSet-U (f _) q<r fUr))
      handle (inj-r (s , t , q' , xLs , xUt , q'<q , close-U)) =
        inj-r (s , t , q , xLs , xUt , q<r ,
               (\y s<y y<t -> Real.isUpperSet-U (f _) q'<q (close-U y s<y y<t)))

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-bind handle
      where
      handle : ((U'0< q ⊎ U'<0 q) ⊎ U'ε q) -> ∃[ r ∈ ℚ ] ((r < q) × U r)
      handle (inj-l (inj-l (xL0 , fUq))) = ∥-map handle2 (Real.isLowerOpen-U (f _) q fUq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((r < q) × Real.U (f _) r) -> Σ[ r ∈ ℚ ] ((r < q) × U r)
        handle2 (r , r<q , fUr) = r , r<q , ∣ inj-l (inj-l (xL0 , fUr)) ∣
      handle (inj-l (inj-r (xU0 , fUq))) = ∥-map handle2 (Real.isLowerOpen-U (f _) q fUq)
        where
        handle2 : Σ[ r ∈ ℚ ] ((r < q) × Real.U (f _) r) -> Σ[ r ∈ ℚ ] ((r < q) × U r)
        handle2 (r , r<q , fUr) = r , r<q , ∣ inj-l (inj-r (xU0 , fUr)) ∣
      handle (inj-r ((s , s<0) , (t , 0<t) , q' , xLs , xUt , q'<q , close-U)) =
        ∣ mean q' q , mean-<₂ q'<q ,
          ∣ inj-r ((s , s<0) , (t , 0<t) , q' , xLs , xUt , mean-<₁ q'<q , close-U) ∣ ∣







    disjoint : Universal (Comp (L ∩ U))
    disjoint q (Lq , Uq) = unsquash isPropBot (∥-map2 handle Lq Uq)
      where
      handle : (L'0< q ⊎ L'<0 q) ⊎ L'ε q -> (U'0< q ⊎ U'<0 q) ⊎ U'ε q -> Bot
      handle (inj-l (inj-l (_ , fxLq))) (inj-l (inj-l (_ , fxUq))) =
        Real.disjoint (f _) q (subst (\fx -> Real.L fx q) fx-path fxLq , fxUq)
      handle (inj-l (inj-r (_ , fxLq))) (inj-l (inj-r (_ , fxUq))) =
        Real.disjoint (f _) q (subst (\fx -> Real.L fx q) fx-path fxLq , fxUq)
      handle (inj-l (inj-l (xL0 , _))) (inj-l (inj-r (xU0 , _))) =
        Real.disjoint x 0# (xL0 , xU0)
      handle (inj-l (inj-r (xU0 , _))) (inj-l (inj-l (xL0 , _))) =
        Real.disjoint x 0# (xL0 , xU0)
      handle (inj-l (inj-l (xL0 , fxLq)))
             (inj-r ((r , r<0) , (s , 0<s) , t , xLr , xUs , t<q , close)) =
        unsquash isPropBot (∥-map handle2 (Real.isUpperOpen-L fx q fxLq))
        where
        fx = f⁺ x (L->ℝ< xL0)
        handle2 : Σ[ q' ∈ ℚ ] (q < q' × Real.L fx q') -> Bot
        handle2 (q' , q<q' , fxLq') = Real.disjoint fx q' (fxLq' , fxUq')
          where
          fxUq' : Real.U fx q'
          fxUq' = closeℝ-U close (trans-< t<q q<q') _ xLr xUs
      handle (inj-l (inj-r (xU0 , fxLq)))
             (inj-r ((r , r<0) , (s , 0<s) , t , xLr , xUs , t<q , close)) =
        unsquash isPropBot (∥-map handle2 (Real.isUpperOpen-L fx q fxLq))
        where
        fx = f⁻ x (U->ℝ< xU0)
        handle2 : Σ[ q' ∈ ℚ ] (q < q' × Real.L fx q') -> Bot
        handle2 (q' , q<q' , fxLq') = Real.disjoint fx q' (fxLq' , fxUq')
          where
          fxUq' : Real.U fx q'
          fxUq' = closeℝ-U close (trans-< t<q q<q') _ xLr xUs
      handle (inj-r ((r , r<0) , (s , 0<s) , t , xLr , xUs , q<t , close))
             (inj-l (inj-l (xL0 , fxUq)))  =
        unsquash isPropBot (∥-map handle2 (Real.isLowerOpen-U fx q fxUq))
        where
        fx = f⁺ x (L->ℝ< xL0)
        handle2 : Σ[ q' ∈ ℚ ] (q' < q × Real.U fx q') -> Bot
        handle2 (q' , q'<q , fxUq') = Real.disjoint fx q' (fxLq' , fxUq')
          where
          fxLq' : Real.L fx q'
          fxLq' = closeℝ-L close (trans-< q'<q q<t) _ xLr xUs
      handle (inj-r ((r , r<0) , (s , 0<s) , t , xLr , xUs , q<t , close))
             (inj-l (inj-r (xU0 , fxUq)))  =
        unsquash isPropBot (∥-map handle2 (Real.isLowerOpen-U fx q fxUq))
        where
        fx = f⁻ x (U->ℝ< xU0)
        handle2 : Σ[ q' ∈ ℚ ] (q' < q × Real.U fx q') -> Bot
        handle2 (q' , q'<q , fxUq') = Real.disjoint fx q' (fxLq' , fxUq')
          where
          fxLq' : Real.L fx q'
          fxLq' = closeℝ-L close (trans-< q'<q q<t) _ xLr xUs
      handle (inj-r ((r1 , r1<0) , (s1 , 0<s1) , t1 , xLr1 , xUs1 , q<t1 , close1))
             (inj-r ((r2 , r2<0) , (s2 , 0<s2) , t2 , xLr2 , xUs2 , t2<q , close2)) =
        asym-< q<f0 f0<q
        where
        q<f0 : ℚ->ℝ q < fℚ 0#
        q<f0 = trans-< (ℚ->ℝ-preserves-< q<t1) (L->ℝ< (close1 0# r1<0 0<s1))
        f0<q : fℚ 0# < ℚ->ℝ q
        f0<q = trans-< (U->ℝ< (close2 0# r2<0 0<s2)) (ℚ->ℝ-preserves-< t2<q)


    located⁺ : x.L 0# -> (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located⁺ xL0 q r q<r = ∥-map handle (fx.located q r q<r)
      where
      fx = (f⁺ x (L->ℝ< xL0))
      module fx = Real fx
      handle : fx.L q ⊎ fx.U r -> L q ⊎ U r
      handle (inj-l fxLq) = inj-l ∣ (inj-l (inj-l (xL0 , fxLq))) ∣
      handle (inj-r fxUr) = inj-r ∣ (inj-l (inj-l (xL0 , fxUr))) ∣


    located⁻ : x.U 0# -> (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located⁻ xU0 q r q<r = ∥-map handle (fx.located q r q<r)
      where
      fx = (f⁻ x (U->ℝ< xU0))
      module fx = Real fx
      handle : fx.L q ⊎ fx.U r -> L q ⊎ U r
      handle (inj-l fxLq) = inj-l ∣ (inj-l (inj-r (xU0 , fxLq))) ∣
      handle (inj-r fxUr) = inj-r ∣ (inj-l (inj-r (xU0 , fxUr))) ∣


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
      f0 = f 0∈
      module f0 = Real f0
      handle : (f0.L q' ⊎ f0.U r') -> Ans
      handle (inj-l f0Lq') = ∥-bind handle2 (isContinuous-lower-bound ℝ≤≥0S cont-f 0∈ q'<f0)
        where
        q'<f0 = L->ℝ< f0Lq'
        handle2 : (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype ℝ≤≥0S) ->
                                       distance 0# y < δ -> ℚ->ℝ q' < f y∈) ->
                  Ans
        handle2 (δ1⁺@(δ1 , 0<δ1) , δ1close) = ∥-bind handle3 0<δ1
          where
          handle3 : 0# ℝ<' δ1 -> Ans
          handle3 (ℝ<'-cons δ2 0U-δ2 δ1L-δ2) =
            ∥-bind handle4 (split-distance<ε 0# x (ℚ->ℝ δ2 , 0<δ2))
            where
            0<δ2 = U->ℝ< 0U-δ2

            handle4 : Tri⊎ (0# < x) (distance 0# x < (ℚ->ℝ δ2)) (x < 0#) -> Ans
            handle4 (tri⊎-< 0<x)   = located⁺ (ℝ<->L 0<x) q r q<r
            handle4 (tri⊎-> x<0)   = located⁻ (ℝ<->U x<0) q r q<r
            handle4 (tri⊎-= d0x<δ2) =
              ∣ inj-l (∣ inj-r (δ2⁻ , δ2⁺ , q' , ℝ<->L -δ2<x , ℝ<->U x<δ2 , q<q' , δ2close ) ∣) ∣
              where
              0<δ2ℚ = U->ℚ< 0U-δ2
              δ2⁺ = δ2 , 0<δ2ℚ
              δ2⁻ = - δ2 , minus-flips-0< 0<δ2ℚ
              x<δ2 : x < ℚ->ℝ δ2
              x<δ2 = trans-=-< (sym diff-step >=> +-left-zero) (trans-≤-< max-≤-left d0x<δ2)
              -δ2<x : ℚ->ℝ (- δ2) < x
              -δ2<x =
                trans-=-< ℚ->ℝ-preserves--
                  (trans-<-=
                    (minus-flips-<
                      (trans-=-< (sym +-left-zero >=> diff-anticommute)
                                 (trans-≤-< max-≤-right d0x<δ2)))
                    minus-double-inverse)
              δ2close : (t : ℚ) -> (- δ2) < t -> t < δ2 -> Real.L (fℚ t) q'
              δ2close t -δ2<t t<δ2 = ℝ<->L (δ1close (ℚ->ℝ≤≥0 t) (trans-< dis-0t<δ2 (L->ℝ< δ1L-δ2)))
                where
                dif-0t<δ2 : diff 0# (ℚ->ℝ t) < ℚ->ℝ δ2
                dif-0t<δ2 = trans-=-< (sym +-left-zero >=> diff-step) (ℚ->ℝ-preserves-< t<δ2)
                dif-t0<δ2 : diff (ℚ->ℝ t) 0# < ℚ->ℝ δ2
                dif-t0<δ2 =
                  trans-=-< (+-left-zero)
                    (trans-<-= (minus-flips-< (ℚ->ℝ-preserves-< -δ2<t))
                      (cong -_ ℚ->ℝ-preserves-- >=> minus-double-inverse))

                dis-0t<δ2 : distance 0# (ℚ->ℝ t) < ℚ->ℝ δ2
                dis-0t<δ2 = max-least-< dif-0t<δ2 (trans-=-< (sym diff-anticommute) dif-t0<δ2)
      handle (inj-r f0Ur') = ∥-bind handle2 (isContinuous-upper-bound ℝ≤≥0S cont-f 0∈ f0<r')
        where
        f0<r' = U->ℝ< f0Ur'
        handle2 : (Σ[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype ℝ≤≥0S) ->
                                       distance 0# y < δ -> f y∈ < ℚ->ℝ r') ->
                  Ans
        handle2 (δ1⁺@(δ1 , 0<δ1) , δ1close) = ∥-bind handle3 0<δ1
          where
          handle3 : 0# ℝ<' δ1 -> Ans
          handle3 (ℝ<'-cons δ2 0U-δ2 δ1L-δ2) =
            ∥-bind handle4 (split-distance<ε 0# x (ℚ->ℝ δ2 , 0<δ2))
            where
            0<δ2 = U->ℝ< 0U-δ2

            handle4 : Tri⊎ (0# < x) (distance 0# x < (ℚ->ℝ δ2)) (x < 0#) -> Ans
            handle4 (tri⊎-< 0<x)   = located⁺ (ℝ<->L 0<x) q r q<r
            handle4 (tri⊎-> x<0)   = located⁻ (ℝ<->U x<0) q r q<r
            handle4 (tri⊎-= d0x<δ2) =
              ∣ inj-r (∣ inj-r (δ2⁻ , δ2⁺ , r' , ℝ<->L -δ2<x , ℝ<->U x<δ2 , r'<r , δ2close ) ∣) ∣
              where
              0<δ2ℚ = U->ℚ< 0U-δ2
              δ2⁺ = δ2 , 0<δ2ℚ
              δ2⁻ = - δ2 , minus-flips-0< 0<δ2ℚ
              x<δ2 : x < ℚ->ℝ δ2
              x<δ2 = trans-=-< (sym diff-step >=> +-left-zero) (trans-≤-< max-≤-left d0x<δ2)
              -δ2<x : ℚ->ℝ (- δ2) < x
              -δ2<x =
                trans-=-< ℚ->ℝ-preserves--
                  (trans-<-=
                    (minus-flips-<
                      (trans-=-< (sym +-left-zero >=> diff-anticommute)
                                 (trans-≤-< max-≤-right d0x<δ2)))
                    minus-double-inverse)
              δ2close : (t : ℚ) -> (- δ2) < t -> t < δ2 -> Real.U (fℚ t) r'
              δ2close t -δ2<t t<δ2 = ℝ<->U (δ1close (ℚ->ℝ≤≥0 t) (trans-< dis-0t<δ2 (L->ℝ< δ1L-δ2)))
                where
                dif-0t<δ2 : diff 0# (ℚ->ℝ t) < ℚ->ℝ δ2
                dif-0t<δ2 = trans-=-< (sym +-left-zero >=> diff-step) (ℚ->ℝ-preserves-< t<δ2)
                dif-t0<δ2 : diff (ℚ->ℝ t) 0# < ℚ->ℝ δ2
                dif-t0<δ2 =
                  trans-=-< (+-left-zero)
                    (trans-<-= (minus-flips-< (ℚ->ℝ-preserves-< -δ2<t))
                      (cong -_ ℚ->ℝ-preserves-- >=> minus-double-inverse))

                dis-0t<δ2 : distance 0# (ℚ->ℝ t) < ℚ->ℝ δ2
                dis-0t<δ2 = max-least-< dif-0t<δ2 (trans-=-< (sym diff-anticommute) dif-t0<δ2)

  glue-≤≥0 : ℝ
  glue-≤≥0 = record
    { L = L
    ; U = U
    ; isProp-L = \_ -> squash
    ; isProp-U = \_ -> squash
    ; Inhabited-L = Inhabited-L
    ; Inhabited-U = Inhabited-U
    ; isLowerSet-L = isLowerSet-L
    ; isUpperSet-U = isUpperSet-U
    ; isUpperOpen-L = isUpperOpen-L
    ; isLowerOpen-U = isLowerOpen-U
    ; disjoint = disjoint
    ; located = located
    }
-}
