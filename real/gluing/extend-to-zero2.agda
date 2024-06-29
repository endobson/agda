{-# OPTIONS --cubical --safe --exact-split #-}

module real.gluing.extend-to-zero2 where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import heyting-field.instances.real
open import heyting-field.instances.rational
open import nat
open import order
open import metric-space
open import metric-space.continuous
open import metric-space.instances.subspace
open import metric-space.instances.real
open import order.instances.real
open import order.instances.nat
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.real
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-field
open import ordered-field.mean
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import real
open import real.apartness
open import real.distance
open import real.order
open import real.complete
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.subspace
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import subset.subspace
open import truncation
open import net
open import metric-space.complete

ℚ⁺-DirectedSet : DirectedSet ℓ-zero ℓ-zero
ℚ⁺-DirectedSet .DirectedSet.Index = ℚ⁺
ℚ⁺-DirectedSet .DirectedSet.isSet-Index = isSetΣ isSetℚ (\_ -> isProp->isSet isProp-<)
ℚ⁺-DirectedSet .DirectedSet.R (q , _) (r , _) = q ≥ r
ℚ⁺-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.isProp-≼ = isProp-≤
ℚ⁺-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.refl-≼ = refl-≤
ℚ⁺-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.trans-≼ lt1 lt2 = trans-≤ lt2 lt1
ℚ⁺-DirectedSet .DirectedSet.isDirected-R .isDirected.∃upper-bound (q , 0<q) (r , 0<r) =
  ∣ (min q r , min-greatest-< 0<q 0<r) , min-≤-left , min-≤-right ∣


module _
  (f : (x : ℝ⁺) -> ℝ)
  (cont-f : isContinuous f)
  {lim : ℝ}
  (isLimit-lim : isLimitAt f 0# lim ℓ-zero ℓ-zero)
  ((x , 0≤x) : ℝ⁰⁺)
  where
  private
    n1 : Net ℝ⁺ ℓ-zero ℓ-zero
    n1 .Net.directed-set = ℚ⁺-DirectedSet
    n1 .Net.f (q , 0<q) = (x + ℚ->ℝ q , 0<xq)
      where
      0<xq : 0# < (x + ℚ->ℝ q)
      0<xq = trans-≤-< (trans-≤-= 0≤x (sym +-right-zero))
                       (+₁-preserves-< (ℚ->ℝ-preserves-< 0<q))
    module n1 = Net n1


    isLimit-n1 : isLimitS n1 x
    isLimit-n1 .isLimitS.close ε⁺@(ε , 0<ε) = ∥-map handle 0<ε
      where
      handle : 0# ℝ<' ε -> isEventuallyΣ n1 (\ (y , _) -> εClose ε⁺ x y)
      handle (ℝ<'-cons ε' 0U-ε' εL-ε') = (ε' , 0<ε') , close
        where
        0<ε' : 0# < ε'
        0<ε' = U->ℚ< 0U-ε'
        ε'<ε : ℚ->ℝ ε' < ε
        ε'<ε = L->ℝ< εL-ε'
        close : ((q , _) : ℚ⁺) -> q ≤ ε' -> εClose ε⁺ x (x + ℚ->ℝ q)
        close (q , 0<q) q≤ε' =
          trans-=-< (cong abs diff-x-xq >=> abs-0≤-path (ℚ->ℝ-preserves-≤ (weaken-< 0<q)))
                    (trans-≤-< (ℚ->ℝ-preserves-≤ q≤ε') ε'<ε)
          where
          diff-x-xq : diff x (x + ℚ->ℝ q) == ℚ->ℝ q
          diff-x-xq = +-assoc >=> diff-step

    isLimit'-n1 : (0<x : 0# < x) -> isLimit n1 (x , 0<x)
    isLimit'-n1 0<x .isLimit.close = isLimitS.close isLimit-n1

    n2 : Net ℝ ℓ-zero ℓ-zero
    n2 = Net-map f n1


    module n2 = Net n2

    isCauchy-n2⁺ : 0# < x -> isCauchy n2
    isCauchy-n2⁺ 0<x ε⁺@(ε , 0<ε) =
      ∥-bind handle (isContinuous.at cont-f (x , 0<x) ε/2⁺)
      where
      ε/2 = 1/2 * ε
      0<ε/2 = *-preserves-0< 0<1/2 0<ε
      ε/2⁺ = ε/2 , 0<ε/2
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ⁺) -> εClose δ x y -> εClose ε/2⁺ (f (x , 0<x)) (f y∈)) ->
               _
      handle (δ⁺@(δ , 0<δ) , close-x) = ∥-bind handle2 0<δ
        where
        handle2 : _ -> _
        handle2 (ℝ<'-cons δ' 0U-δ' δL-δ') = ∣ i , close ∣
          where
          i : ℚ⁺
          i = (δ' , U->ℚ< 0U-δ')
          δ'<δ : ℚ->ℝ δ' < δ
          δ'<δ = L->ℝ< δL-δ'
          close : ∀ i2 i3 -> n1.≼ i i2 -> n1.≼ i i3 -> εClose ε⁺ (f (n1.f i2)) (f (n1.f i3))
          close i2 i3 i≼i2 i≼i3 =
            trans-≤-<
              (trans-≤-= (distance-triangleᵉ (f (n1.f i2)) (f (x , 0<x)) (f (n1.f i3)))
                         (+-left (distance-commuteᵉ (f (n1.f i2)) (f (x , 0<x)))))
              (trans-<-= (+-preserves-< (close-x (n1.f i2) d2<δ)
                                        (close-x (n1.f i3) d3<δ))
                         1/2-path)
            where
            x2 = Subspace.value (n1.f i2)
            x3 = Subspace.value (n1.f i3)
            -- 0<x2 = Subspace.prop (n1.f i2)
            -- 0<x3 = Subspace.prop (n1.f i3)

            d2<δ : distance x x2 < δ
            d2<δ =
              trans-=-<
                (cong abs (+-assoc >=> diff-step) >=>
                 abs-0≤-path (ℚ->ℝ-preserves-≤ (weaken-< (snd i2))))
                (trans-≤-< (ℚ->ℝ-preserves-≤ i≼i2) δ'<δ)
            d3<δ : distance x x3 < δ
            d3<δ =
              trans-=-<
                (cong abs (+-assoc >=> diff-step) >=>
                 abs-0≤-path (ℚ->ℝ-preserves-≤ (weaken-< (snd i3))))
                (trans-≤-< (ℚ->ℝ-preserves-≤ i≼i3) δ'<δ)


    isCauchy-n2 : isCauchy n2
    isCauchy-n2 ε⁺@(ε , 0<ε) = ∥-bind handle (isLimitAt.close isLimit-lim ε/2⁺)
      where
      ε/2 = 1/2 * ε
      0<ε/2 = *-preserves-0< 0<1/2 0<ε
      ε/2⁺ = ε/2 , 0<ε/2
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ⁺) -> εClose δ 0# y -> εClose ε/2⁺ lim (f y∈)) ->
               _
      handle (δ⁺@(δ , 0<δ) , close0) = ∥-bind handle2 (split-distance<ε 0# x δ⁺)
        where
        handle2 : _ -> _
        handle2 (tri⊎-< x<0) = bot-elim (0≤x x<0)
        handle2 (tri⊎-> 0<x) = isCauchy-n2⁺ 0<x ε⁺
        handle2 (tri⊎-= dx<δ) = ∥-map handle3 (isLimitS.close isLimit-n1 (δ2 , 0<δ2))
          where
          x<δ : x < δ
          x<δ = distance0-<⁻ dx<δ
          δ2 = diff x δ
          0<δ2 : 0# < δ2
          0<δ2 = diff-0<⁺ x<δ
          handle3 : _ -> _
          handle3 (i , close-x) = (i , close-n2)
            where
            close-n2 : ∀ i2 i3 -> n1.≼ i i2 -> n1.≼ i i3 -> εClose ε⁺ (f (n1.f i2)) (f (n1.f i3))
            close-n2 i2 i3 i≼i2 i≼i3 =
              trans-≤-<
                (trans-≤-= (distance-triangleᵉ (f (n1.f i2)) lim (f (n1.f i3)))
                           (+-left (distance-commuteᵉ (f (n1.f i2)) lim)))
                (trans-<-= (+-preserves-< (close0 (n1.f i2) (distance0-<⁺ (weaken-< 0<x2) x2<δ))
                                          (close0 (n1.f i3) (distance0-<⁺ (weaken-< 0<x3) x3<δ)))
                           1/2-path)
              where
              x2 = Subspace.value (n1.f i2)
              0<x2 = Subspace.prop (n1.f i2)
              x3 = Subspace.value (n1.f i3)
              0<x3 = Subspace.prop (n1.f i3)

              d2<δ2 : εClose (δ2 , 0<δ2) x x2
              d2<δ2 = close-x i2 i≼i2
              x2<δ : x2 < δ
              x2<δ = distance-diff-<₁ d2<δ2
              d3<δ2 : εClose (δ2 , 0<δ2) x x3
              d3<δ2 = close-x i3 i≼i3
              x3<δ : x3 < δ
              x3<δ = distance-diff-<₁ d3<δ2

  extend-0< : ℝ
  extend-0< = fst (isComplete₀-ℝ n2 isCauchy-n2)

  private
    y = extend-0<
    isLimit-y : isLimit n2 y
    isLimit-y = snd (isComplete₀-ℝ n2 isCauchy-n2)

    isLimit-fx : (0<x : 0# < x) -> isLimit n2 (f (x , 0<x))
    isLimit-fx 0<x = isContinuous-preserves-isLimit cont-f (isLimit'-n1 0<x)

    isLimit-n2-lim : (x == 0#) -> isLimit n2 lim
    isLimit-n2-lim x=0 = isLimitAt->isLimit∀Net isLimit-lim n1 (subst (isLimitS n1) x=0 isLimit-n1)
