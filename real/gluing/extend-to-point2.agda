{-# OPTIONS --cubical --safe --exact-split #-}

module real.gluing.extend-to-point2 where

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
open import real.gluing.extend-to-zero2
open import real.apartness
open import real.arithmetic.rational
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
open import sum
open import filter


-- ℚ#0 : Type₀
-- ℚ#0 = Σ[ q ∈ ℚ ] (q <> 0#)
--
-- ℚ#0-DirectedSet : DirectedSet ℓ-zero ℓ-zero
-- ℚ#0-DirectedSet .DirectedSet.Index = ℚ#0
-- ℚ#0-DirectedSet .DirectedSet.isSet-Index = isSetΣ isSetℚ (\_ -> isProp->isSet isProp-<>)
-- ℚ#0-DirectedSet .DirectedSet.R (q , _) (r , _) = abs q ≥ abs r
-- ℚ#0-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.isProp-≼ = isProp-≤
-- ℚ#0-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.refl-≼ = refl-≤
-- ℚ#0-DirectedSet .DirectedSet.isPreOrder-R .isPreOrder.trans-≼ lt1 lt2 = trans-≤ lt2 lt1
-- ℚ#0-DirectedSet .DirectedSet.isDirected-R .isDirected.∃upper-bound (q , q<>0) (r , r<>0) =
--   ∣ (m , (inj-r (min-greatest-< 0<aq 0<ar))) , m≤aq , m≤ar ∣
--   where
--   m : ℚ
--   m = min (abs q) (abs r)
--   0<aq : 0# < abs q
--   0<aq = either (\ q<0 -> trans-<-≤ (minus-flips-<0 q<0) max-≤-right)
--                 (\ 0<q -> trans-<-≤ 0<q max-≤-left) q<>0
--   0<ar : 0# < abs r
--   0<ar = either (\ r<0 -> trans-<-≤ (minus-flips-<0 r<0) max-≤-right)
--                 (\ 0<r -> trans-<-≤ 0<r max-≤-left) r<>0
--   m≤aq : abs m ≤ abs q
--   m≤aq = trans-=-≤ (abs-0≤-path (min-greatest-≤ abs-0≤ abs-0≤)) min-≤-left
--   m≤ar : abs m ≤ abs r
--   m≤ar = trans-=-≤ (abs-0≤-path (min-greatest-≤ abs-0≤ abs-0≤)) min-≤-right

ℚ->ℝ-preserves-max : {a b : ℚ} -> ℚ->ℝ (max a b) == max (ℚ->ℝ a) (ℚ->ℝ b)
ℚ->ℝ-preserves-max {a} {b} =
  antisym-≤ ans ans2

  where
  ans : ¬ (max (ℚ->ℝ a) (ℚ->ℝ b) < ℚ->ℝ (max a b))
  ans lt = irrefl-< (max-least-< a<ab b<ab)
    where
    a<ab : a < max a b
    a<ab = ℚ->ℝ-reflects-< (trans-≤-< max-≤-left lt)
    b<ab : b < max a b
    b<ab = ℚ->ℝ-reflects-< (trans-≤-< max-≤-right lt)

  ans2 : max (ℚ->ℝ a) (ℚ->ℝ b) ≤ ℚ->ℝ (max a b)
  ans2 = max-least-≤ (ℚ->ℝ-preserves-≤ max-≤-left) (ℚ->ℝ-preserves-≤ max-≤-right)

ℚ->ℝ-preserves-abs : {a : ℚ} -> ℚ->ℝ (abs a) == abs (ℚ->ℝ a)
ℚ->ℝ-preserves-abs =  ℚ->ℝ-preserves-max >=> cong2 max refl ℚ->ℝ-preserves--


module _
  (a : ℝ)
  (f : (x : ℝ# a) -> ℝ)
  (cont-f : isContinuous f)
  {lim : ℝ}
  -- (isLimit-lim : isLimitAt f a lim ℓ-zero ℓ-zero)
  (x : ℝ)
  (magic : Magic)
  where

  private
    f1 : Filter (Subspace (ℝ#S a)) ℓ-zero ℓ-one
    f1 .Filter.P S = ∃[ ε ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ# a) -> εClose ε x y -> ⟨ S y∈ ⟩)
    f1 .Filter.isProp-P x = squash
    f1 .Filter.inhabited = ∣ (UnivS (ℝ# a)) , ∣ (1# , 0<1) , (\ _ _ -> tt) ∣ ∣
    f1 .Filter.upward-closed S1 S2 f =
      ∥-map (\ (ε , close) -> ε , \y εC -> f _ (close y εC))
    f1 .Filter.downward-directed S1 S2 = ∥-map2 handle
      where
      handle : Σ[ ε ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ# a) -> εClose ε x y -> ⟨ S1 y∈ ⟩) ->
               Σ[ ε ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ# a) -> εClose ε x y -> ⟨ S2 y∈ ⟩) ->
               _
      handle ((ε1 , 0<ε1) , close1) ((ε2 , 0<ε2) , close2) = S∩ , P∩ , (\_ -> proj₁) , (\_ -> proj₂)
        where
        S∩ = Subtype-∩ S1 S2
        P∩ : ∃[ ε ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ# a) -> εClose ε x y -> ⟨ S∩ y∈ ⟩)
        P∩ = ∣ (min ε1 ε2 , (trans-=-< (sym min-idempotent) (min-preserves-< 0<ε1 0<ε2))) ,
               (\ y∈ εC -> close1 y∈ (trans-<-≤ εC min-≤-left) ,
                           close2 y∈ (trans-<-≤ εC min-≤-right)) ∣

    f2 : Filter ℝ ℓ-zero ℓ-one
    f2 = Filter-map f f1

    ConvergesTo-f1-x : (x#a : x # a) -> ConvergesTo f1 (x , x#a)
    ConvergesTo-f1-x x#a .ConvergesTo.contains S Sx =
      ?



--    n1 : Net (Subspace (ℝ#S a)) ℓ-zero ℓ-zero
--    n1 .Net.directed-set = ℚ#0-DirectedSet
--    n1 .Net.f (q , q<>0) = (a + ℚ->ℝ q) , a+q#a
--      where
--      a+q#a : (a + ℚ->ℝ q) # a
--      a+q#a =
--        subst ((a + ℚ->ℝ q) #_) +-right-zero
--          (+₁-preserves-# (⊎-map ℚ->ℝ-preserves-< ℚ->ℝ-preserves-< q<>0))
--
--    isLimit-n1 : isLimitS n1 a
--    isLimit-n1 .isLimitS.close ε⁺@(ε , 0<ε) = ∥-map handle 0<ε
--      where
--      handle : 0# ℝ<' ε -> isEventuallyΣ n1 (\ (y , _) -> εClose ε⁺ a y)
--      handle (ℝ<'-cons ε' 0U-ε' εL-ε') = (ε' , inj-r 0<ε') , close
--        where
--        0<ε' : 0# < ε'
--        0<ε' = U->ℚ< 0U-ε'
--        0ℝ<ε' : 0# < ℚ->ℝ ε'
--        0ℝ<ε' = U->ℝ< 0U-ε'
--        ε'<ε : ℚ->ℝ ε' < ε
--        ε'<ε = L->ℝ< εL-ε'
--        close : ((q , _) : ℚ#0) -> abs q ≤ abs ε' -> εClose ε⁺ a (a + ℚ->ℝ q)
--        close (q , 0<q) aq≤aε' =
--          trans-=-< (cong abs diff-a-aq >=> sym ℚ->ℝ-preserves-abs)
--            (trans-≤-< (ℚ->ℝ-preserves-≤ aq≤aε')
--              (trans-=-< (ℚ->ℝ-preserves-abs >=> (abs-0≤-path (weaken-< 0ℝ<ε'))) ε'<ε))
--          where
--          diff-a-aq : diff a (a + ℚ->ℝ q) == ℚ->ℝ q
--          diff-a-aq = +-assoc >=> diff-step

--    n2 : Net ℝ ℓ-zero ℓ-zero
--    n2 = Net-map f n1

    -- isCauchy-n2# : x#a < x -> isCauchy n2
    -- isCauchy-n2# 0<x ε⁺@(ε , 0<ε) =
    --   ∥-bind handle (isContinuous.at cont-f (x , 0<x) ε/2⁺)
    --   where
    --   ε/2 = 1/2 * ε
    --   0<ε/2 = *-preserves-0< 0<1/2 0<ε
    --   ε/2⁺ = ε/2 , 0<ε/2
    --   handle : Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : ℝ⁺) -> εClose δ x y -> εClose ε/2⁺ (f (x , 0<x)) (f y∈)) ->
    --            _
    --   handle (δ⁺@(δ , 0<δ) , close-x) = ∥-bind handle2 0<δ
    --     where
    --     handle2 : _ -> _
    --     handle2 (ℝ<'-cons δ' 0U-δ' δL-δ') = ∣ i , close ∣
    --       where
    --       i : ℚ⁺
    --       i = (δ' , U->ℚ< 0U-δ')
    --       δ'<δ : ℚ->ℝ δ' < δ
    --       δ'<δ = L->ℝ< δL-δ'
    --       close : ∀ i2 i3 -> n1.≼ i i2 -> n1.≼ i i3 -> εClose ε⁺ (f (n1.f i2)) (f (n1.f i3))
    --       close i2 i3 i≼i2 i≼i3 =
    --         trans-≤-<
    --           (trans-≤-= (distance-triangleᵉ (f (n1.f i2)) (f (x , 0<x)) (f (n1.f i3)))
    --                      (+-left (distance-commuteᵉ (f (n1.f i2)) (f (x , 0<x)))))
    --           (trans-<-= (+-preserves-< (close-x (n1.f i2) d2<δ)
    --                                     (close-x (n1.f i3) d3<δ))
    --                      1/2-path)
    --         where
    --         x2 = Subspace.value (n1.f i2)
    --         x3 = Subspace.value (n1.f i3)

    --         d2<δ : distance x x2 < δ
    --         d2<δ =
    --           trans-=-<
    --             (cong abs (+-assoc >=> diff-step) >=>
    --              abs-0≤-path (ℚ->ℝ-preserves-≤ (weaken-< (snd i2))))
    --             (trans-≤-< (ℚ->ℝ-preserves-≤ i≼i2) δ'<δ)
    --         d3<δ : distance x x3 < δ
    --         d3<δ =
    --           trans-=-<
    --             (cong abs (+-assoc >=> diff-step) >=>
    --              abs-0≤-path (ℚ->ℝ-preserves-≤ (weaken-< (snd i3))))
    --             (trans-≤-< (ℚ->ℝ-preserves-≤ i≼i3) δ'<δ)
