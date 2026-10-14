{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.multiplication-uniform where

open import additive-group
open import additive-group.instances.real
open import base
open import nat
open import equivalence
open import fin
open import funext
open import functions
open import finite-commutative-monoid
open import equality
open import heyting-field.instances.real
open import metric-space
open import metric-space.ball-subspace
open import metric-space.continuous
open import metric-space.uniformly-continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import ordered-additive-group.absolute-value
open import nat.order
open import finset
open import finsum
open import order.instances.real
open import order.instances.nat
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-ring.absolute-value
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import real
open import real.arithmetic.multiplication.inverse
open import real.distance
open import real.subspace
open import ring
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import subset.subspace
open import truncation





module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  opaque
    isUniformlyContinuous-* : {f g : D -> ℝ} ->
      ∃[ bf ∈ ℝ ] (∀ x -> abs (f x) ≤ bf) ->
      ∃[ bg ∈ ℝ ] (∀ x -> abs (g x) ≤ bg) ->
      isUniformlyContinuous f ->
      isUniformlyContinuous g ->
      isUniformlyContinuous (\x -> f x * g x)
    isUniformlyContinuous-* {f} {g} ∃bf ∃bg ucf ucg =
      unsquash (isProp-isUniformlyContinuous) (∥-map2 handle ∃bf ∃bg)
      where
      handle :
        Σ[ bf ∈ ℝ ] (∀ x -> abs (f x) ≤ bf) ->
        Σ[ bg ∈ ℝ ] (∀ x -> abs (g x) ≤ bg) ->
        isUniformlyContinuous (\x -> f x * g x)
      handle (bf , fx≤bf) (bg , gx≤bg) = isUniformlyContinuous-cons close
        where
        bf' : ℝ
        bf' = max bf 1#
        bg' : ℝ
        bg' = max bg 1#

        0<bf' : 0# < bf'
        0<bf' = trans-<-≤ 0<1 max-≤-right
        0<bg' : 0# < bg'
        0<bg' = trans-<-≤ 0<1 max-≤-right
        1/bf' : ℝ
        1/bf' = ℝ1/ (bf' , inj-r 0<bf')
        1/bg' : ℝ
        1/bg' = ℝ1/ (bg' , inj-r 0<bg')

        0<1/bf' : 0# < 1/bf'
        0<1/bf' = ℝ1/-preserves-0< 0<bf'
        0<1/bg' : 0# < 1/bg'
        0<1/bg' = ℝ1/-preserves-0< 0<bg'


        fg : D -> ℝ
        fg x = f x * g x
        close : ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℝ⁺ ] ∀ x₁ x₂ -> εClose δ x₁ x₂ -> εClose ε (fg x₁) (fg x₂)
        close ε⁺@(ε , 0<ε) =
          ∥-map2 handle2 (isUniformlyContinuous.close ucf εf⁺) (isUniformlyContinuous.close ucg εg⁺)
          where
          ε/2 ε/4 : ℝ
          ε/2 = ε * 1/2
          ε/4 = ε/2 * 1/2
          0<ε/2 : 0# < ε/2
          0<ε/2 = *-preserves-0< 0<ε 0<1/2
          0<ε/4 : 0# < ε/4
          0<ε/4 = *-preserves-0< 0<ε/2 0<1/2
          ε/2<ε : ε/2 < ε
          ε/2<ε = trans-<-= (*₁-preserves-< 0<ε 1/2<1) *-right-one

          εf : ℝ
          εf = 1/bg' * ε/4
          0<εf : 0# < εf
          0<εf = *-preserves-0< 0<1/bg' 0<ε/4
          εf⁺ : ℝ⁺
          εf⁺ = εf , 0<εf
          εg : ℝ
          εg = 1/bf' * ε/4
          0<εg : 0# < εg
          0<εg = *-preserves-0< 0<1/bf' 0<ε/4
          εg⁺ : ℝ⁺
          εg⁺ = εg , 0<εg


          handle2 : Σ[ δf ∈ ℝ⁺ ] (∀ x₁ x₂ -> εClose δf x₁ x₂ -> εClose εf⁺ (f x₁) (f x₂)) ->
                    Σ[ δg ∈ ℝ⁺ ] (∀ x₁ x₂ -> εClose δg x₁ x₂ -> εClose εg⁺ (g x₁) (g x₂)) ->
                    Σ[ δ ∈ ℝ⁺ ] ∀ x₁ x₂ -> εClose δ x₁ x₂ -> εClose ε⁺ (fg x₁) (fg x₂)
          handle2 ((δf , 0<δf) , f-close) ((δg , 0<δg) , g-close) = δfg⁺ , fg-close
            where
            δfg⁺ : ℝ⁺
            δfg⁺ = min δf δg , min-greatest-< 0<δf 0<δg

            fg-close : ∀ x₁ x₂ -> εClose δfg⁺ x₁ x₂ -> εClose ε⁺ (fg x₁) (fg x₂)
            fg-close x₁ x₂ dx<δfg = trans-≤-< lt₁ ε/2<ε
              where
              p₁ : diff (fg x₁) (fg x₂) ==
                   f x₂ * diff (g x₁) (g x₂) + g x₁ * (diff (f x₁) (f x₂))
              p₁ = sym +-right-zero >=>
                   +-right (sym +-inverse) >=>
                   +-right +-commute >=>
                   +-swap >=>
                   +-right +-commute >=>
                   +-left (sym *-distrib-diff-left) >=>
                   +-right (sym *-distrib-diff-right >=> *-commute)

              lt₂ : (abs (f x₂) * distance (g x₁) (g x₂)) ≤ ε/4
              lt₂ =
                trans-≤
                  (trans-≤
                    (*₁-preserves-≤ abs-0≤ (weaken-< (g-close x₁ x₂ (trans-<-≤ dx<δfg min-≤-right))))
                    (*₂-preserves-≤ (fx≤bf x₂) (weaken-< 0<εg)))
                  (trans-≤-=
                    (trans-=-≤ (sym *-assoc) (*₂-preserves-≤ bf-lt (weaken-< 0<ε/4)))
                    *-left-one)

                where
                bf-lt : (bf * 1/bf') ≤ 1#
                bf-lt = trans-≤-= (*₂-preserves-≤ max-≤-left (weaken-< 0<1/bf'))
                                  (*-commute >=> ℝ1/-inverse)

              lt₃ : (abs (g x₁) * distance (f x₁) (f x₂)) ≤ ε/4
              lt₃ =
                trans-≤
                  (trans-≤
                    (*₁-preserves-≤ abs-0≤ (weaken-< (f-close x₁ x₂ (trans-<-≤ dx<δfg min-≤-left))))
                    (*₂-preserves-≤ (gx≤bg x₁) (weaken-< 0<εf)))
                  (trans-≤-=
                    (trans-=-≤ (sym *-assoc) (*₂-preserves-≤ bg-lt (weaken-< 0<ε/4)))
                    *-left-one)

                where
                bg-lt : (bg * 1/bg') ≤ 1#
                bg-lt = trans-≤-= (*₂-preserves-≤ max-≤-left (weaken-< 0<1/bg'))
                                  (*-commute >=> ℝ1/-inverse)


              lt₁ : distance (fg x₁) (fg x₂) ≤ ε/2
              lt₁ =
                trans-≤
                  (trans-≤ (trans-=-≤ (cong abs p₁) abs-distrib-+)
                           (path-≤ (+-cong abs-distrib-* abs-distrib-*)))
                  (trans-≤-= (+-preserves-≤ lt₂ lt₃) +-/2-path)
