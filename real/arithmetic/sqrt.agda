{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.sqrt where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import order
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring.sqrt
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import ordered-semiring.squares
open import rational
open import rational.order
open import rational.proper-interval
open import rational.proper-interval.containment
open import rational.proper-interval.multiplication-inclusion
open import real
open import real.arithmetic.multiplication
open import real.arithmetic.sqrt.base
open import real.interval
open import real.rational
open import ring.implementations.real
open import semiring
open import truncation

private
  module _ (x : ℝ) (x≮0 : x ≮ 0#) where
    ≮0-sqrtᵉ : (sqrtℝᵉ x x≮0) ≮ 0#
    ≮0-sqrtᵉ s<0 = ℝ≮0-¬U0 x x≮0 xU-0
      where
      s = (sqrtℝᵉ x x≮0)
      module s = Real s
      module x = Real x
      sU-0 : s.U 0#
      sU-0 = ℝ<->U s<0
      xU-0 : x.U 0#
      xU-0 = subst x.U *-right-zero (snd (sU-0))

    opaque
      unfolding sqrtℝ

      ≮0-sqrt : (sqrtℝ x x≮0) ≮ 0#
      ≮0-sqrt = ≮0-sqrtᵉ

module _ (x : ℝ) (x≮0 : x ≮ 0#) where
  private
    sx = (sqrtℝᵉ x x≮0)
    sxsx = sx ℝ*ᵉ sx
    module x = Real x
    module sx = Real sx

    ℝ∈Iℚ-sqrtᵉ⁻ : (xi yi : Iℚ) -> ℝ∈Iℚ sx xi -> ℝ∈Iℚ sx yi -> ℝ∈Iℚ x (xi i* yi)
    ℝ∈Iℚ-sqrtᵉ⁻ xi@(Iℚ-cons xl xu xl<xu) yi@(Iℚ-cons yl yu yl<yu)
                sx∈xi@(sx-lx , sx-ux) sx∈yi@(sx-ly , sx-uy) =
      unsquash (isProp-ℝ∈Iℚ x (xi i* yi))
        (∥-map (\(ti , ti⊂xyi , sx∈ti) -> x-l ti ti⊂xyi sx∈ti , x-u ti ti⊂xyi sx∈ti)
          (tighter-ℝ∈Iℚ sx xyi sx∈xyi))
      where
      xyi-o = ℝ∈Iℚ->Overlap sx xi yi sx∈xi sx∈yi
      xyi = i-intersect xi yi xyi-o
      sx∈xyi : ℝ∈Iℚ sx xyi
      sx∈xyi = ℝ∈Iℚ-intersect sx xi yi sx∈xi sx∈yi

      xyi⊆xi : xyi i⊆ xi
      xyi⊆xi = i-intersect-⊆₁ xi yi xyi-o
      xyi⊆yi : xyi i⊆ yi
      xyi⊆yi = i-intersect-⊆₂ xi yi xyi-o

      module _ (ti@(Iℚ-cons til tiu til<tiu) : Iℚ)
               (ti⊂xyi@(i⊂-cons xyi-l<til tiu<xyi-u) : ti i⊂ xyi)
               (sx∈ti : ℝ∈Iℚ sx ti) where
        xiyi = xi i* yi
        xiyi-l = Iℚ.l xiyi
        xiyi-u = Iℚ.u xiyi

        0≤tiu : 0# ≤ tiu
        0≤tiu = (fst (snd sx∈ti))

        ti⊂xi : ti i⊂ xi
        ti⊂xi = trans-i⊂-i⊆ ti⊂xyi xyi⊆xi
        ti⊂yi : ti i⊂ yi
        ti⊂yi = trans-i⊂-i⊆ ti⊂xyi xyi⊆yi

        ti²⊂xiyi : (ti i* ti) i⊂ xiyi
        ti²⊂xiyi = i*-preserves-⊂ ti⊂xi ti⊂yi

        x-u : x.U xiyi-u
        x-u =
          x.isUpperSet-U
            (trans-≤-< (trans-≤ max-≤-right max-≤-right) (_i⊂_.u ti²⊂xiyi))
            (snd (snd sx∈ti))

        x-l : x.L xiyi-l
        x-l = handle (fst sx∈ti)
          where
          handle : (til < 0r ⊎ ((0r ≤ til) × (x.L (til * til)))) -> x.L xiyi-l
          handle (inj-l til<0) = ℝ≮0-L∀<0 x x≮0 xiyi-l<0
            where
            tiul≤0 : (tiu * til) ≤ 0#
            tiul≤0 = *₁-preserves-≤0 0≤tiu (weaken-< til<0)
            xiyi-l<0 : xiyi-l < 0#
            xiyi-l<0 = trans-<-≤ (_i⊂_.l ti²⊂xiyi) (trans-≤ (trans-≤ min-≤-right min-≤-left) tiul≤0)
          handle (inj-r (_ , xL-til²)) =
            x.isLowerSet-L (trans-<-≤ (_i⊂_.l ti²⊂xiyi) (trans-≤ min-≤-left min-≤-left))
              xL-til²


    *-sqrtᵉ : sxsx == x
    *-sqrtᵉ = ℝ∈Iℚ->path (sx ℝ*ᵉ sx) x f
      where
      f : (a : Iℚ) -> ℝ∈Iℚ sxsx a -> ℝ∈Iℚ x a
      f a@(Iℚ-cons l u l≤u) (sxsx-lq , sxsx-uq) =
        unsquash (isProp-ℝ∈Iℚ x a) (∥-map2 handle sxsx-lq sxsx-uq)
        where
        handle : Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ sx xi × ℝ∈Iℚ sx yi × i-Lower (xi i* yi) l) ->
                 Σ[ zi ∈ Iℚ ] Σ[ wi ∈ Iℚ ] (ℝ∈Iℚ sx zi × ℝ∈Iℚ sx wi × i-Upper (zi i* wi) u) ->
                 ℝ∈Iℚ x a
        handle (xi , yi , sx∈xi , sx∈yi , l≤xyi) (zi , wi , sx∈zi , sx∈wi , zwi≤u) =
          isLowerSet≤ x l≤xyi (fst x∈xyi) ,
          isUpperSet≤ x zwi≤u (snd x∈zwi)
          where
          xyi = xi i* yi
          x∈xyi : ℝ∈Iℚ x xyi
          x∈xyi = ℝ∈Iℚ-sqrtᵉ⁻ xi yi sx∈xi sx∈yi

          zwi = zi i* wi
          x∈zwi : ℝ∈Iℚ x (zi i* wi)
          x∈zwi = ℝ∈Iℚ-sqrtᵉ⁻ zi wi sx∈zi sx∈wi

  opaque
    unfolding sqrtℝ

    sqrt² : (sqrtℝ x x≮0) * (sqrtℝ x x≮0) == x
    sqrt² = ℝ*-eval >=> *-sqrtᵉ

∃!sqrt : (x : ℝ) -> (0# ≤ x) -> ∃![ y ∈ ℝ ] (0# ≤ y × (y * y == x))
∃!sqrt x 0≤x = (sqrtℝ x 0≤x , ≮0-sqrt x 0≤x , sqrt² x 0≤x) , isProp-Σsqrt _


module _ (x : ℝ) (x≮0 : x ≮ 0#) where
  private
    sx = ∃!-val (∃!sqrt x x≮0)

  opaque
    sqrt-0< : (0<x : 0# < x) -> 0# < sx
    sqrt-0< 0<x = isSqrt-0< (∃!-prop (∃!sqrt x x≮0)) 0<x

    sqrt-0≤ : 0# ≤ sx
    sqrt-0≤ = isSqrt-0≤ (∃!-prop (∃!sqrt x x≮0))

module _ (x : ℝ) where
  opaque
    sqrt-square : sqrtℝ (x * x) square-≮0 == abs x
    sqrt-square = isSqrt-square (∃!-prop (∃!sqrt (x * x) square-≮0))

module _ (x : ℝ) (y : ℝ) (x≮0 : x ≮ 0#) (y≮0 : y ≮ 0#)
  where
  private
    xy = x * y
    0≤xy : 0# ≤ xy
    0≤xy = *-preserves-≮0 x≮0 y≮0
    sx = (sqrtℝ x x≮0)
    sy = (sqrtℝ y y≮0)
    sxy = (sqrtℝ xy 0≤xy)
    sxsy = sx ℝ* sy

  opaque
    sqrt-* : sxy == sxsy
    sqrt-* = ∃!-unique (∃!sqrt (x * y) 0≤xy) sxsy (isSqrt-* (∃!-prop (∃!sqrt x x≮0))
                                                            (∃!-prop (∃!sqrt y y≮0)))
