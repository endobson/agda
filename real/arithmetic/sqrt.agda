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
open import rational.minmax
open import rational.order
open import rational.proper-interval
open import rational.proper-interval.abs
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
      sU-0 = ℝ<->U s 0# s<0
      xU-0 : x.U 0#
      xU-0 = subst x.U *-right-zero (snd (sU-0))

    ≮0-sqrt : (sqrtℝ x x≮0) ≮ 0#
    ≮0-sqrt = subst (_≮ 0#) (sym (sqrtℝ-eval x x≮0)) ≮0-sqrtᵉ

  ℚ∈Iℚ-i-intersect₁ : (q : ℚ) (a b : Iℚ) -> (o : Overlap a b) ->
                      ℚ∈Iℚ q (i-intersect a b o) -> ℚ∈Iℚ q a
  ℚ∈Iℚ-i-intersect₁ q a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) o (il≤q , q≤iu) =
    trans-≤ max-≤-left il≤q , trans-≤ q≤iu min-≤-left

  ℚ∈Iℚ-i-intersect₂ : (q : ℚ) (a b : Iℚ) -> (o : Overlap a b) ->
                      ℚ∈Iℚ q (i-intersect a b o) -> ℚ∈Iℚ q b
  ℚ∈Iℚ-i-intersect₂ q a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) o (il≤q , q≤iu) =
    trans-≤ max-≤-right il≤q , trans-≤ q≤iu min-≤-right

module _ (x : ℝ) (x≮0 : x ≮ 0#) where
  private
    sx = (sqrtℝᵉ x x≮0)
    sxsx = sx ℝ*ᵉ sx
    module x = Real x
    module sx = Real sx

    ℝ∈Iℚ-sqrtᵉ⁻ : (xi yi : Iℚ) -> ℝ∈Iℚ sx xi -> ℝ∈Iℚ sx yi -> ℝ∈Iℚ x (xi i* yi)
    ℝ∈Iℚ-sqrtᵉ⁻ xi@(Iℚ-cons xl xu xl≤xu) yi@(Iℚ-cons yl yu yl≤yu)
                sx∈xi@(sx-lx , sx-ux) sx∈yi@(sx-ly , sx-uy) = x-l1 , x-u2
      where
      xyi-o = ℝ∈Iℚ->Overlap sx xi yi sx∈xi sx∈yi
      xyi = i-intersect xi yi xyi-o
      sx∈xyi = ℝ∈Iℚ-intersect sx xi yi sx∈xi sx∈yi
      xyi-l = Iℚ.l xyi
      xyi-u = Iℚ.u xyi
      xyi-l≤u = Iℚ.l≤u xyi

      xiyi = xi i* yi
      xiyi-l = Iℚ.l xiyi
      xiyi-u = Iℚ.u xiyi

      0<xu : 0r < xu
      0<xu = strengthen-ℚ≤-≠ (fst sx-ux) 0!=xu
        where
        0!=xu : 0r != xu
        0!=xu 0=xu = ℝ≮0-¬U0 sx (≮0-sqrtᵉ x x≮0) (subst sx.U (sym 0=xu) sx-ux)

      0<yu : 0r < yu
      0<yu = strengthen-ℚ≤-≠ (fst sx-uy) 0!=yu
        where
        0!=yu : 0r != yu
        0!=yu 0=yu = ℝ≮0-¬U0 sx (≮0-sqrtᵉ x x≮0) (subst sx.U (sym 0=yu) sx-uy)

      x-u1 : x.U (xyi-u * xyi-u)
      x-u1 = snd (snd sx∈xyi)

      xyi-u²∈xiyi : ℚ∈Iℚ (xyi-u * xyi-u) xiyi
      xyi-u²∈xiyi = ℚ∈Iℚ-* xyi-u xyi-u xi yi ∈xi ∈yi
        where
        ∈xi : ℚ∈Iℚ xyi-u xi
        ∈xi = ℚ∈Iℚ-i-intersect₁ xyi-u xi yi xyi-o (xyi-l≤u , refl-≤)
        ∈yi : ℚ∈Iℚ xyi-u yi
        ∈yi = ℚ∈Iℚ-i-intersect₂ xyi-u xi yi xyi-o (xyi-l≤u , refl-≤)

      x-u2 : x.U xiyi-u
      x-u2 = isUpperSet≤ x (snd xyi-u²∈xiyi) x-u1

      x-l1 : x.L xiyi-l
      x-l1 = handle (fst sx∈xi) (fst sx∈yi)
        where
        handle : (xl < 0r ⊎ ((0r ≤ xl) × (x.L (xl * xl)))) ->
                 (yl < 0r ⊎ ((0r ≤ yl) × (x.L (yl * yl)))) ->
                 x.L xiyi-l
        handle (inj-l xl<0) _ = ℝ≮0-L∀<0 x x≮0 xiyi-l<0
          where
          xl∈xi : ℚ∈Iℚ xl xi
          xl∈xi = refl-≤ , xl≤xu
          yu∈yi : ℚ∈Iℚ yu yi
          yu∈yi = yl≤yu , refl-≤
          xlyu<0 : (xl * yu) < 0r
          xlyu<0 = *₂-preserves-<0 xl<0 0<yu

          xiyi-l≤xlyu : xiyi-l ≤ (xl * yu)
          xiyi-l≤xlyu = fst (ℚ∈Iℚ-* xl yu xi yi xl∈xi yu∈yi)
          xiyi-l<0 = trans-≤-< xiyi-l≤xlyu xlyu<0
        handle (inj-r _) (inj-l yl<0) = ℝ≮0-L∀<0 x x≮0 xiyi-l<0
          where
          xu∈xi : ℚ∈Iℚ xu xi
          xu∈xi = xl≤xu , refl-≤
          yl∈yi : ℚ∈Iℚ yl yi
          yl∈yi = refl-≤ , yl≤yu
          xuyl<0 : (xu * yl) < 0r
          xuyl<0 = *₁-preserves-<0 0<xu yl<0

          xiyi-l≤xuyl : xiyi-l ≤ (xu * yl)
          xiyi-l≤xuyl = fst (ℚ∈Iℚ-* xu yl xi yi xu∈xi yl∈yi)
          xiyi-l<0 = trans-≤-< xiyi-l≤xuyl xuyl<0

        handle (inj-r (0≤xl , xL-xl²)) (inj-r (0≤yl , xL-yl²)) =
          isLowerSet≤ x (fst xyi-l²∈xiyi) x-l2
          where

          x-l2 : x.L (xyi-l * xyi-l)
          x-l2 = maxℚ-property {P = \z -> x.L (z * z)} xl yl xL-xl² xL-yl²

          xyi-l²∈xiyi : ℚ∈Iℚ (xyi-l * xyi-l) xiyi
          xyi-l²∈xiyi = ℚ∈Iℚ-* xyi-l xyi-l xi yi ∈xi ∈yi
            where
            ∈xi : ℚ∈Iℚ xyi-l xi
            ∈xi = ℚ∈Iℚ-i-intersect₁ xyi-l xi yi xyi-o (refl-≤ , xyi-l≤u)
            ∈yi : ℚ∈Iℚ xyi-l yi
            ∈yi = ℚ∈Iℚ-i-intersect₂ xyi-l xi yi xyi-o (refl-≤ , xyi-l≤u)



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

  abstract
    sqrt² : (sqrtℝ x x≮0) * (sqrtℝ x x≮0) == x
    sqrt² = cong2 _ℝ*_ (sqrtℝ-eval x x≮0) (sqrtℝ-eval x x≮0) >=>
            ℝ*-eval {sx} {sx} >=>
            *-sqrtᵉ

∃!sqrt : (x : ℝ) -> (0# ≤ x) -> ∃![ y ∈ ℝ ] (0# ≤ y × (y * y == x))
∃!sqrt x 0≤x = (sqrtℝ x 0≤x , ≮0-sqrt x 0≤x , sqrt² x 0≤x) , isProp-Σsqrt _


module _ (x : ℝ) (x≮0 : x ≮ 0#) where
  private
    sx = ∃!-val (∃!sqrt x x≮0)

  abstract
    sqrt-0< : (0<x : 0# < x) -> 0# < sx
    sqrt-0< 0<x = isSqrt-0< (∃!-prop (∃!sqrt x x≮0)) 0<x

    sqrt-0≤ : 0# ≤ sx
    sqrt-0≤ = isSqrt-0≤ (∃!-prop (∃!sqrt x x≮0))

module _ (x : ℝ) where
  abstract
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

  sqrt-* : sxy == sxsy
  sqrt-* = ∃!-unique (∃!sqrt (x * y) 0≤xy) sxsy (isSqrt-* (∃!-prop (∃!sqrt x x≮0))
                                                          (∃!-prop (∃!sqrt y y≮0)))
