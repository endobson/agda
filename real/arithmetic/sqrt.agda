{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.sqrt where

open import base
open import equality
open import hlevel.sigma
open import hlevel
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-semiring
open import ordered-ring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.proper-interval.abs
open import rational.proper-interval.multiplication-assoc
open import rational.proper-interval
open import rational.order
open import rational.minmax
open import rational.squares
open import real
open import real.arithmetic
open import real.arithmetic.sqrt.base
open import real.arithmetic.multiplication
open import real.arithmetic.absolute-value
open import real.interval
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sign
open import sign.instances.rational
open import sum
open import truncation

module _ (x : ℝ) (x≮0 : x ≮ 0ℝ) where
  ≮0-sqrtᵉ : (sqrtℝᵉ x x≮0) ≮ 0ℝ
  ≮0-sqrtᵉ s<0 = ℝ≮0-¬U0 x x≮0 xU-0
    where
    s = (sqrtℝᵉ x x≮0)
    module s = Real s
    module x = Real x
    sU-0 : s.U 0r
    sU-0 = ℝ<->U s 0r s<0
    xU-0 : x.U 0r
    xU-0 = subst x.U *-right-zero (snd (sU-0))

  ≮0-sqrt : (sqrtℝ x x≮0) ≮ 0ℝ
  ≮0-sqrt = subst (_≮ 0ℝ) (sym (sqrtℝ-eval x x≮0)) ≮0-sqrtᵉ

ℚ∈Iℚ-i-intersect₁ : (q : ℚ) (a b : Iℚ) -> (o : Overlap a b) ->
                    ℚ∈Iℚ q (i-intersect a b o) -> ℚ∈Iℚ q a
ℚ∈Iℚ-i-intersect₁ q a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) o (il≤q , q≤iu) =
  trans-≤ (maxℚ-≤-left al bl) il≤q , trans-≤ q≤iu (minℚ-≤-left au bu)

ℚ∈Iℚ-i-intersect₂ : (q : ℚ) (a b : Iℚ) -> (o : Overlap a b) ->
                    ℚ∈Iℚ q (i-intersect a b o) -> ℚ∈Iℚ q b
ℚ∈Iℚ-i-intersect₂ q a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) o (il≤q , q≤iu) =
  trans-≤ (maxℚ-≤-right al bl) il≤q , trans-≤ q≤iu (minℚ-≤-right au bu)


private
  module _ (x : ℝ) where
    private
      xx = x ℝ*ᵉ x
      module x = Real x
      module xx = Real xx

    ≮0-squareᵉ : xx ≮ 0ℝ
    ≮0-squareᵉ x²<0 = unsquash isPropBot (∥-bind handle x²<0)
      where
      handle : xx ℝ<' 0ℝ -> ∥ Bot ∥
      handle (ℝ<'-cons q xxU-q q<0) = ∥-map handle2 xxU-q
        where
        handle2 : Σ[ ai ∈ Iℚ ] Σ[ bi ∈ Iℚ ] (ℝ∈Iℚ x ai × ℝ∈Iℚ x bi × i-Upper (ai i* bi) q) -> Bot
        handle2 (ai , bi , x∈ai , x∈bi , abi≤q) = irrefl-< (trans-<-≤ uu<0 0≤-square)
          where
          ai*bi = ai i* bi

          abi-o = ℝ∈Iℚ->Overlap x ai bi x∈ai x∈bi
          ai∩bi = i-intersect ai bi abi-o
          x∈ai∩bi = ℝ∈Iℚ-intersect x ai bi x∈ai x∈bi
          u = Iℚ.u ai∩bi
          u∈ai∩bi : ℚ∈Iℚ u ai∩bi
          u∈ai∩bi = Iℚ.l≤u ai∩bi , refl-≤
          u∈ai = ℚ∈Iℚ-i-intersect₁ u ai bi abi-o u∈ai∩bi
          u∈bi = ℚ∈Iℚ-i-intersect₂ u ai bi abi-o u∈ai∩bi
          uu∈ai*bi : ℚ∈Iℚ (u * u) ai*bi
          uu∈ai*bi = ℚ∈Iℚ-* u u ai bi u∈ai u∈bi
          uu<0 : (u * u) < 0r
          uu<0 = trans-≤-< (trans-≤ (snd uu∈ai*bi) abi≤q) (L->ℚ< q<0)

abstract
  ≮0-square : (x : ℝ) -> (x * x) ≮ 0ℝ
  ≮0-square x = subst (_≮ 0ℝ) (sym (ℝ*-eval {x} {x})) (≮0-squareᵉ x)

  absℝ-square : (x : ℝ) -> x * x == absℝ x * absℝ x
  absℝ-square x = sym (absℝ-NonNeg-idem (x * x) (≮0-square x)) >=> absℝ-distrib-* x x

  absℝ-zero : {x : ℝ} -> absℝ x == 0ℝ -> x == 0ℝ
  absℝ-zero {x} p = sym (absℝ-NonNeg-idem x 0≤x) >=> p
    where
    0≤x : 0ℝ ≤ x
    0≤x x<0 = irrefl-< {_} {_} {_} {0ℝ} (subst2 _<_ x0=0 xx=0 x0<xx)
      where
      x0<xx : (x * 0ℝ) < (x * x)
      x0<xx = *₁-flips-< x x 0ℝ x<0 x<0
      xx=0 : x * x == 0ℝ
      xx=0 = absℝ-square x >=> *-right p >=> *-right-zero
      x0=0 : x * 0ℝ == 0ℝ
      x0=0 = *-right-zero

  -- absℝ-NonNeg-idem : (x : ℝ) -> (x ≮ 0ℝ) -> absℝ x == x


module _ (x : ℝ) (x≮0 : x ≮ 0ℝ) where
  private
    sx = sqrtℝ x x≮0
    sxᵉ = sqrtℝᵉ x x≮0
    module x = Real x
    module sx = Real sx
    module sxᵉ = Real sxᵉ

    sqrt-0<ᵉ : (0<x : 0ℝ < x) -> 0ℝ < sxᵉ
    sqrt-0<ᵉ 0<x = ∥-bind handle 0<x
      where
      handle : 0ℝ ℝ<' x -> 0ℝ ℝ< sxᵉ
      handle (ℝ<'-cons q 0<q xL-q) = ∥-map handle2 (squares-dense-0 (U->ℚ< 0<q))
        where
        handle2 : Σ[ s ∈ ℚ ] (isSquareℚ s × 0r < s × s < q) -> 0ℝ ℝ<' sxᵉ
        handle2 (s , (t , 0≤t , tt=s) , 0<s , s<q) =
          ℝ<'-cons t (ℚ<->U (strengthen-ℚ≤-≠ 0≤t 0!=t))
                     (inj-r (0≤t , (subst x.L (sym tt=s) (x.isLowerSet-L s q s<q xL-q))))
          where
          0!=t : 0r != t
          0!=t 0=t = <->!= 0<s (sym *-right-zero >=> *-right 0=t >=> tt=s)

  abstract
    sqrt-0< : (0<x : 0ℝ < x) -> 0ℝ < sx
    sqrt-0< 0<x = subst (0ℝ <_) (sym (sqrtℝ-eval x x≮0)) (sqrt-0<ᵉ 0<x)

module _ (x : ℝ) (x≮0 : x ≮ 0ℝ) where
  private
    sx = sqrtℝ x x≮0
    sxᵉ = sqrtℝᵉ x x≮0
    module x = Real x
    module sx = Real sx
    module sxᵉ = Real sxᵉ

    sqrt-0≤ᵉ : sxᵉ ≮ 0ℝ
    sqrt-0≤ᵉ sx<0 = unsquash isPropBot (∥-map handle sx<0)
      where
      handle : sxᵉ ℝ<' 0ℝ -> Bot
      handle (ℝ<'-cons q sxU-q q<0) = sxᵉ.disjoint q (inj-l (L->ℚ< q<0) , sxU-q)

  abstract
    sqrt-0≤ : 0ℝ ≤ sx
    sqrt-0≤ = subst (0ℝ ≤_) (sym (sqrtℝ-eval x x≮0)) sqrt-0≤ᵉ


module _ (x : ℝ) where
  private
    xx = x ℝ*ᵉ x
    module x = Real x
    module xx = Real xx

  module _ (≮0 : xx ≮ 0ℝ) where
    private
      sxx = (sqrtℝᵉ xx ≮0)
      module sxx = Real sxx

    ℝ∈Iℚ-sqrt⁺ : (ai : Iℚ) -> ImbalancedI ai -> ℝ∈Iℚ x ai -> ℝ∈Iℚ sxx ai
    ℝ∈Iℚ-sqrt⁺ ai@(Iℚ-cons al au al≤au) -al≤au x∈ai@(xL-al , xU-au) = handle (split-< al 0r)
      where
      0≤au : 0r ≤ au
      0≤au = ImbalancedI->0≤u ai -al≤au

      xxU-auau : xx.U (au * au)
      xxU-auau = ∣ ai , ai , x∈ai , x∈ai , aiai≤auau ∣
        where
          aiai≤auau : Iℚ.u (ai i* ai) ≤ (au * au)
          aiai≤auau = maxℚ-property {P = \x -> x ≤ (au * au)} _ _ alai≤auau auai≤auau
            where
            alau≤auau = *₂-preserves-≤ al au au al≤au 0≤au
            alal≤auau = handle (split-< al 0r)
              where
              handle : (al < 0r ⊎ 0r ≤ al) -> (al * al) ≤ (au * au)
              handle (inj-r 0≤al) =
                trans-≤ (*₁-preserves-≤ al al au 0≤al al≤au)
                        (*₂-preserves-≤ al au au al≤au 0≤au)
              handle (inj-l al<0) = subst (_≤ (au * au)) -al-al=alal -al-al≤auau
                where
                0≤-al = minus-flips-≤0 (weaken-< al<0)
                -al = - al

                -al-al≤auau = trans-≤ (*₁-preserves-≤ -al -al au 0≤-al -al≤au)
                                      (*₂-preserves-≤ -al au au -al≤au 0≤au)
                -al-al=alal : (-al * -al) == al * al
                -al-al=alal = minus-extract-left >=> cong -_ minus-extract-right >=> minus-double-inverse


            alai≤auau : Iℚ.u (i-scale al ai) ≤ (au * au)
            alai≤auau =
              maxℚ-property {P = \x -> x ≤ (au * au)} (al * al) (al * au) alal≤auau alau≤auau

            auai≤auau : Iℚ.u (i-scale au ai) ≤ (au * au)
            auai≤auau = subst (\x -> Iℚ.u x ≤ (au * au)) (i-scale-NN-path (au , 0≤-NonNeg au 0≤au) ai)
                              refl-≤
      handle : (al < 0r ⊎ 0r ≤ al) -> ℝ∈Iℚ sxx ai
      handle (inj-l al<0) = (inj-l al<0       , (0≤au , xxU-auau))
      handle (inj-r 0≤al) = (inj-r (0≤al , xxL-alal) , (0≤au , xxU-auau))
        where
        xxL-alal : xx.L (al * al)
        xxL-alal = ∣ ai , ai , x∈ai , x∈ai , alal≤aiai ∣
          where
          alal≤aiai : (al * al) ≤ Iℚ.l (ai i* ai)
          alal≤aiai = minℚ-property {P = \x -> (al * al) ≤ x} _ _ alal≤alai alal≤auai
            where
            alal≤alai : (al * al) ≤ Iℚ.l (i-scale al ai)
            alal≤alai = subst (\x -> (al * al) ≤ Iℚ.l x) (i-scale-NN-path (al , 0≤-NonNeg al 0≤al) ai)
                              refl-≤
            alal≤auai : (al * al) ≤ Iℚ.l (i-scale au ai)
            alal≤auai = subst (\x -> (al * al) ≤ Iℚ.l x) (i-scale-NN-path (au , 0≤-NonNeg au 0≤au) ai)
                              (*₂-preserves-≤ al au al al≤au 0≤al)

module _ (x : ℝ) where
  private
    xx = x ℝ*ᵉ x
    module x = Real x
    module xx = Real xx

    sqrt-*ᵉ : (≮0 : xx ≮ 0ℝ) -> sqrtℝᵉ xx ≮0 == absℝ x
    sqrt-*ᵉ ≮0 = sym (ℝ∈Iℚ->path (absℝ x) (sqrtℝᵉ xx ≮0) ℝ∈Iℚ-sqrt-abs)
      where
      mx = (- x)
      -x-x≮0 = ≮0-squareᵉ mx
      sxx = (sqrtℝᵉ xx ≮0)
      s-x-x = (sqrtℝᵉ (mx ℝ*ᵉ mx) -x-x≮0)
      module sxx = Real sxx

      p : (mx ℝ*ᵉ mx) == (x ℝ*ᵉ x)
      p = p1 >=> minus-extract-left {_} {_} {_} {x} {mx} >=>
          cong -_ (minus-extract-right {_} {_} {_} {x} {x}) >=>
          minus-double-inverse {_} {_} {_} {x * x}>=>
          p5
        where
        abstract
          p1 : (mx ℝ*ᵉ mx) == (mx ℝ* mx)
          p1 = sym (ℝ*-eval {mx} {mx})
          p5 : (x ℝ* x) == (x ℝ*ᵉ x)
          p5 = (ℝ*-eval {x} {x})

      sp : sxx == s-x-x
      sp = cong2-dep sqrtℝᵉ (sym p) (isProp->PathP (\_ -> (isProp¬ _)) ≮0 -x-x≮0)


      ℝ∈Iℚ-sqrt-abs : (ai : Iℚ) -> ℝ∈Iℚ (absℝ x) ai -> ℝ∈Iℚ sxx ai
      ℝ∈Iℚ-sqrt-abs ai ax∈ai = handle (ℝ∈Iℚ-absℝ-ΣImbalancedI x ai ax∈ai)
        where
        handle : Σ[ bi ∈ Iℚ ] (ℝ∈Iℚ (absℝ x) bi × ImbalancedI bi × (bi i⊆ ai)) -> ℝ∈Iℚ sxx ai
        handle (bi , ax∈bi , imb-bi , bi⊆ai) =
          ℝ∈Iℚ-⊆ sxx bi⊆ai (unsquash (isProp-ℝ∈Iℚ sxx bi) (∥-map handle2 (ℝ∈Iℚ-absℝ⁻ x bi ax∈bi)))
          where
          handle2 : (ℝ∈Iℚ x bi) ⊎ (ℝ∈Iℚ x (i- bi)) -> ℝ∈Iℚ sxx bi
          handle2 (inj-l x∈bi) = (ℝ∈Iℚ-sqrt⁺ x ≮0 bi imb-bi x∈bi)
          handle2 (inj-r x∈-bi) = (subst (\z -> ℝ∈Iℚ z bi) (sym sp) s-x-x∈bi)
            where
            -x∈bi : ℝ∈Iℚ mx bi
            -x∈bi = subst (ℝ∈Iℚ mx) (i--double-inverse {bi}) (ℝ∈Iℚ-- x (i- bi) x∈-bi)

            s-x-x∈bi : ℝ∈Iℚ (sqrtℝᵉ (mx ℝ*ᵉ mx) -x-x≮0) bi
            s-x-x∈bi = (ℝ∈Iℚ-sqrt⁺ mx -x-x≮0 bi imb-bi -x∈bi)

  abstract
    sqrt-square : sqrtℝ (x * x) (≮0-square x) == absℝ x
    sqrt-square =
      sqrtℝ-eval (x * x) (≮0-square x) >=>
      cong2-dep sqrtℝᵉ (ℝ*-eval {x} {x})
                (isProp->PathP (\_ -> (isProp¬ _)) (≮0-square x) (≮0-squareᵉ x)) >=>
      sqrt-*ᵉ (≮0-squareᵉ x)

module _ (x : ℝ) (x≮0 : x ≮ 0ℝ) where
  private
    sx = (sqrtℝᵉ x x≮0)
    sxsx = sx ℝ*ᵉ sx
    module x = Real x
    module sx = Real sx
    module sxsx = Real sxsx

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
      x-u2 = isUpperSet≤ x (xyi-u * xyi-u) xiyi-u (snd xyi-u²∈xiyi) x-u1

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
          xlyu<0 = r*-Neg-Pos xl<0 0<yu

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
          xuyl<0 = r*-Pos-Neg 0<xu yl<0

          xiyi-l≤xuyl : xiyi-l ≤ (xu * yl)
          xiyi-l≤xuyl = fst (ℚ∈Iℚ-* xu yl xi yi xu∈xi yl∈yi)
          xiyi-l<0 = trans-≤-< xiyi-l≤xuyl xuyl<0

        handle (inj-r (0≤xl , xL-xl²)) (inj-r (0≤yl , xL-yl²)) =
          isLowerSet≤ x xiyi-l (xyi-l * xyi-l) (fst xyi-l²∈xiyi) x-l2
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
          isLowerSet≤ x l (Iℚ.l xyi) l≤xyi (fst x∈xyi) ,
          isUpperSet≤ x (Iℚ.u zwi) u zwi≤u (snd x∈zwi)
          where
          xyi = xi i* yi
          x∈xyi : ℝ∈Iℚ x xyi
          x∈xyi = ℝ∈Iℚ-sqrtᵉ⁻ xi yi sx∈xi sx∈yi

          zwi = zi i* wi
          x∈zwi : ℝ∈Iℚ x (zi i* wi)
          x∈zwi = ℝ∈Iℚ-sqrtᵉ⁻ zi wi sx∈zi sx∈wi

  abstract
    ℝ∈Iℚ-sqrt⁻ : (xi yi : Iℚ) -> ℝ∈Iℚ (sqrtℝ x x≮0) xi -> ℝ∈Iℚ (sqrtℝ x x≮0) yi -> ℝ∈Iℚ x (xi i* yi)
    ℝ∈Iℚ-sqrt⁻ xi yi sx∈xi sx∈yi = ℝ∈Iℚ-sqrtᵉ⁻ xi yi sx∈xi' sx∈yi'
      where
      sx∈xi' = subst (\x -> ℝ∈Iℚ x xi) (sqrtℝ-eval x x≮0) sx∈xi
      sx∈yi' = subst (\x -> ℝ∈Iℚ x yi) (sqrtℝ-eval x x≮0) sx∈yi

    sqrt² : (sqrtℝ x x≮0) * (sqrtℝ x x≮0) == x
    sqrt² = cong2 _ℝ*_ (sqrtℝ-eval x x≮0) (sqrtℝ-eval x x≮0) >=>
            ℝ*-eval {sx} {sx} >=>
            *-sqrtᵉ

private
  split-ℝ∈Iℚ-0≤ : (x : ℝ) (ai : Iℚ) -> ℝ∈Iℚ x ai -> 0ℝ ≤ x ->
                  ∃[ bi ∈ Iℚ ] (ℝ∈Iℚ x bi × bi i⊆ ai × (BalancedI bi ⊎ NonNegI bi))
  split-ℝ∈Iℚ-0≤ x ai@(Iℚ-cons l u l≤u) x∈ai 0≤x = handle (split-< l 0r) (split-< u -l)
    where
    module x = Real x
    -l = - l
    -u = - u
    0<u : 0r < u
    0<u = proj-¬r (split-< 0r u) ¬u≤0
      where
      ¬u≤0 : ¬ (u ≤ 0r)
      ¬u≤0 u≤0 = ℝ≮0-¬U0 x 0≤x (isUpperSet≤ x u 0r u≤0 (snd x∈ai))

    Ans = Σ[ bi ∈ Iℚ ] (ℝ∈Iℚ x bi × bi i⊆ ai × (BalancedI bi ⊎ NonNegI bi))
    Ans' = ∥ Ans ∥
    handle : (l < 0r ⊎ 0r ≤ l) -> (u < -l ⊎ -l ≤ u) -> Ans'
    handle (inj-r 0≤l) _            = ∣ ai , x∈ai , (i⊆-cons refl-≤ refl-≤) , inj-r (0≤-NonNeg l 0≤l) ∣
    handle (inj-l l<0) (inj-r -l≤u) = ∥-map handle2 (x.located 0r -l 0<-l)
      where
      0<-l = minus-flips-<0 l<0
      handle2 : (x.L 0r ⊎ x.U -l) -> Ans
      handle2 (inj-l xL-0) = bi , (xL-0 , snd x∈ai) , i⊆-cons (weaken-< l<0) refl-≤ ,
                             inj-r (0≤-NonNeg 0r refl-≤)
        where
        bi = Iℚ-cons 0r u (weaken-< (trans-<-≤ 0<-l -l≤u))
      handle2 (inj-r xU--l) = bi , (fst x∈ai , xU--l) , i⊆-cons refl-≤ -l≤u , inj-l refl
        where
        bi = Iℚ-cons l -l (weaken-< (trans-< l<0 0<-l))
    handle (inj-l l<0) (inj-l u<-l) = ∥-map handle2 (x.located -u 0r -u<0)
      where
      l<-u = subst (_< -u) minus-double-inverse (minus-flips-< _ _ u<-l)
      -u<0 = minus-flips-0< 0<u
      handle2 : (x.L -u ⊎ x.U 0r) -> Ans
      handle2 (inj-l xL--u) = bi , (xL--u , snd x∈ai) , i⊆-cons (weaken-< l<-u) refl-≤ ,
                              inj-l minus-double-inverse
        where
        bi = Iℚ-cons -u u (weaken-< (trans-< -u<0 0<u))
      handle2 (inj-r xU-0) = bot-elim (ℝ≮0-¬U0 x 0≤x xU-0)


module _ (x : ℝ)
  where
  private
    xx = x ℝ* x
    ax = absℝ x
    mx = - x
    module x = Real x
    module ax = Real ax
    module xx = Real xx


    ℝ∈Iℚ-square-NonNeg⁻ : (ai : Iℚ) -> NonNegI ai -> ℝ∈Iℚ xx (ai i* ai) -> ℝ∈Iℚ ax ai
    ℝ∈Iℚ-square-NonNeg⁻ ai nn-ai xx∈aiai =
      unsquash (isProp-ℝ∈Iℚ ax ai) (∥-map handle (ℝ∈Iℚ-*⁻ x x (ai i* ai) xx∈aiai))
      where
      handle : Σ[ bi ∈ Iℚ ] Σ[ ci ∈ Iℚ ] (ℝ∈Iℚ x bi × ℝ∈Iℚ x ci × (bi i* ci) i⊆ (ai i* ai)) ->
               ℝ∈Iℚ ax ai
      handle (bi , ci , x∈bi , x∈ci , bici⊆aiai) = handle2 (ImbalancedI-i- bci)
        where
        bci-o = ℝ∈Iℚ->Overlap x bi ci x∈bi x∈ci
        bci = i-intersect bi ci bci-o
        mbci = i- bci
        x∈bci = ℝ∈Iℚ-intersect x bi ci x∈bi x∈ci

        bci⊆bi = i-intersect-⊆₁ bi ci bci-o
        bci⊆ci = i-intersect-⊆₂ bi ci bci-o
        bcibci⊆bici = i*-preserves-⊆ bci⊆bi bci⊆ci
        bcibci⊆aiai = trans-i⊆ bcibci⊆bici bici⊆aiai

        mbci²=bci² : mbci i* mbci == (bci i* bci)
        mbci²=bci² = i--extract-both bci bci

        mbcimbci⊆aiai = subst (_i⊆ (ai i* ai)) (sym mbci²=bci²) bcibci⊆aiai
        mx∈mbci = ℝ∈Iℚ-- x bci x∈bci

        handle2 : ImbalancedI bci ⊎ ImbalancedI mbci -> ℝ∈Iℚ ax ai
        handle2 (inj-l imb-bci) =
          ℝ∈Iℚ-absℝ-ImbalancedI x ai (NonNegI->ImbalancedI ai nn-ai) (ℝ∈Iℚ-⊆ x bci⊆ai x∈bci)
          where
          bci⊆ai = i*-i⊆-square-NonNegI2⁻ bci ai imb-bci nn-ai bcibci⊆aiai
        handle2 (inj-r imb-mbci) =
          subst (\x -> ℝ∈Iℚ x ai) (absℝ-- x)
            (ℝ∈Iℚ-absℝ-ImbalancedI mx ai (NonNegI->ImbalancedI ai nn-ai) (ℝ∈Iℚ-⊆ mx mbci⊆ai mx∈mbci))
          where
          mbci⊆ai = i*-i⊆-square-NonNegI2⁻ mbci ai imb-mbci nn-ai mbcimbci⊆aiai

    ℝ∈Iℚ-square-Balanced⁻ : (ai : Iℚ) -> BalancedI ai -> ℝ∈Iℚ xx (ai i* ai) -> ℝ∈Iℚ ax ai
    ℝ∈Iℚ-square-Balanced⁻ ai bal-ai xx∈aiai =
      unsquash (isProp-ℝ∈Iℚ ax ai) (∥-map handle (ℝ∈Iℚ-*⁻ x x (ai i* ai) xx∈aiai))
      where
      handle : Σ[ bi ∈ Iℚ ] Σ[ ci ∈ Iℚ ] (ℝ∈Iℚ x bi × ℝ∈Iℚ x ci × (bi i* ci) i⊆ (ai i* ai)) ->
               ℝ∈Iℚ ax ai
      handle (bi , ci , x∈bi , x∈ci , bici⊆aiai) = handle2 (ImbalancedI-i- bci)
        where
        bci-o = ℝ∈Iℚ->Overlap x bi ci x∈bi x∈ci
        bci = i-intersect bi ci bci-o
        mbci = i- bci
        x∈bci = ℝ∈Iℚ-intersect x bi ci x∈bi x∈ci

        bci⊆bi = i-intersect-⊆₁ bi ci bci-o
        bci⊆ci = i-intersect-⊆₂ bi ci bci-o
        bcibci⊆bici = i*-preserves-⊆ bci⊆bi bci⊆ci
        bcibci⊆aiai = trans-i⊆ bcibci⊆bici bici⊆aiai

        mbci²=bci² : mbci i* mbci == (bci i* bci)
        mbci²=bci² = i--extract-both bci bci

        mbcimbci⊆aiai = subst (_i⊆ (ai i* ai)) (sym mbci²=bci²) bcibci⊆aiai
        mx∈mbci = ℝ∈Iℚ-- x bci x∈bci

        handle2 : ImbalancedI bci ⊎ ImbalancedI mbci -> ℝ∈Iℚ ax ai
        handle2 (inj-l imb-bci) =
          ℝ∈Iℚ-absℝ-ImbalancedI x ai (BalancedI->ImbalancedI ai bal-ai) (ℝ∈Iℚ-⊆ x bci⊆ai x∈bci)
          where
          bci⊆ai = i*-i⊆-square-BalancedI⁻ bci ai bal-ai bcibci⊆aiai
        handle2 (inj-r imb-mbci) =
          subst (\x -> ℝ∈Iℚ x ai) (absℝ-- x)
            (ℝ∈Iℚ-absℝ-ImbalancedI mx ai (BalancedI->ImbalancedI ai bal-ai) (ℝ∈Iℚ-⊆ mx mbci⊆ai mx∈mbci))
          where
          mbci⊆ai = i*-i⊆-square-BalancedI⁻ mbci ai bal-ai mbcimbci⊆aiai


  abstract
    ℝ∈Iℚ-square-ImbalancedI⁻ : (ai : Iℚ) -> ImbalancedI ai -> ℝ∈Iℚ (x * x) (ai i* ai) -> ℝ∈Iℚ ax ai
    ℝ∈Iℚ-square-ImbalancedI⁻ ai@(Iℚ-cons l u l≤u) imb-ai xx∈aiai = handle (split-< l 0r)
      where
      -l = - l
      xxU-uu : xx.U (u * u)
      xxU-uu = subst xx.U (cong Iℚ.u (sym (i²-ImbalancedI-path ai imb-ai))) (snd xx∈aiai)
      handle : (l < 0r ⊎ 0r ≤ l) -> ℝ∈Iℚ ax ai
      handle (inj-r 0≤l) = ℝ∈Iℚ-square-NonNeg⁻ ai (0≤-NonNeg _ 0≤l) xx∈aiai
      handle (inj-l l<0) = handle2 (split-< -l u)
        where
        handle2 : (-l < u ⊎ u ≤ -l) -> ℝ∈Iℚ ax ai
        handle2 (inj-r u≤-l) = ℝ∈Iℚ-square-Balanced⁻ ai -l=u xx∈aiai
          where
          -l=u : BalancedI ai
          -l=u = antisym-≤ imb-ai u≤-l
        handle2 (inj-l -l<u) = unsquash (isProp-ℝ∈Iℚ ax ai) (∥-map handle3 (ax.located -l u -l<u))
          where
          handle3 : ax.L -l ⊎ ax.U u -> ℝ∈Iℚ ax ai
          handle3 (inj-r axU-u) = ax∈ai
            where
            axL-l : ax.L l
            axL-l = ℝ≮0-L∀<0 ax (absℝ-≮0 x) l<0
            ax∈ai : ℝ∈Iℚ ax ai
            ax∈ai = axL-l , axU-u
          handle3 (inj-l axL--l) = ℝ∈Iℚ-⊆ ax bi⊆ai ax∈bi
            where
            0<-l = minus-flips-<0 l<0
            bi = Iℚ-cons -l u imb-ai
            nn-bi = 0≤-NonNeg -l (weaken-< 0<-l)
            bi² = i²-NonNegI bi nn-bi
            bi⊆ai : bi i⊆ ai
            bi⊆ai = i⊆-cons (weaken-< (trans-< l<0 0<-l)) refl-≤

            xxL--l-l : xx.L (-l * -l)
            xxL--l-l = unsquash (xx.isProp-L (-l * -l)) (∥-map handle4 ax.Inhabited-U)
              where
              handle4 : Σ[ u2 ∈ ℚ ] (ax.U u2) -> xx.L (-l * -l)
              handle4 (u2 , axU-u2) = (fst (subst (ℝ∈Iℚ xx) (sym (i²-NonNegI-path ci nn-ci)) xx∈cici))
                where
                l<u2 = ℝ-bounds->ℚ< ax _ _ axL--l axU-u2
                ci = Iℚ-cons -l u2 (weaken-< l<u2)
                nn-ci = 0≤-NonNeg -l (weaken-< 0<-l)
                ax∈ci : ℝ∈Iℚ ax ci
                ax∈ci = axL--l , axU-u2
                xx∈cici : ℝ∈Iℚ xx (ci i* ci)
                xx∈cici = subst (\z -> ℝ∈Iℚ z (ci i* ci)) (sym (absℝ-square x))
                                (ℝ∈Iℚ-* ax ax ci ci ax∈ci ax∈ci)

            xx∈bi² : ℝ∈Iℚ xx bi²
            xx∈bi² = xxL--l-l , xxU-uu
            xx∈bibi : ℝ∈Iℚ xx (bi i* bi)
            xx∈bibi = subst (ℝ∈Iℚ xx) (i²-NonNegI-path bi nn-bi) xx∈bi²
            ax∈bi : ℝ∈Iℚ ax bi
            ax∈bi = ℝ∈Iℚ-square-NonNeg⁻ bi nn-bi xx∈bibi


module _ (x : ℝ) (y : ℝ) (x≮0 : x ≮ 0ℝ) (y≮0 : y ≮ 0ℝ)
  where
  private
    xy = x * y
    0≤xy : 0ℝ ≤ xy
    0≤xy = *-preserves-≮0 x y x≮0 y≮0
    sx = (sqrtℝ x x≮0)
    sy = (sqrtℝ y y≮0)
    sxy = (sqrtℝ xy 0≤xy)
    0≤sx = (sqrt-0≤ x x≮0)
    0≤sy = (sqrt-0≤ y y≮0)
    0≤sxy = (sqrt-0≤ xy 0≤xy)
    sxsy = sx ℝ* sy
    module x = Real x
    module y = Real y
    module sx = Real sx
    module sy = Real sy
    module sxsy = Real sxsy


    ℝ∈Iℚ-sqrt-*-ImbalancedI : (xi yi : Iℚ) -> ℝ∈Iℚ sx xi -> ℝ∈Iℚ sy yi ->
                              ImbalancedI xi -> ImbalancedI yi -> ℝ∈Iℚ sxy (xi i* yi)
    ℝ∈Iℚ-sqrt-*-ImbalancedI xi yi sx∈xi sy∈yi imb-xi imb-yi =
      subst (\z -> ℝ∈Iℚ z (xi i* yi)) (absℝ-NonNeg-idem sxy 0≤sxy)
            (ℝ∈Iℚ-square-ImbalancedI⁻ sxy (xi i* yi) imb-xiyi xy∈2)

      where
      x∈xixi : ℝ∈Iℚ x (xi i* xi)
      x∈xixi = ℝ∈Iℚ-sqrt⁻ x x≮0 xi xi sx∈xi sx∈xi
      y∈yiyi : ℝ∈Iℚ y (yi i* yi)
      y∈yiyi = ℝ∈Iℚ-sqrt⁻ y y≮0 yi yi sy∈yi sy∈yi

      xiyi-swap : ((xi i* xi) i* (yi i* yi)) == ((xi i* yi) i* (xi i* yi))
      xiyi-swap = sym (i*-assoc xi xi (yi i* yi)) >=>
                  cong (xi i*_) (i*-assoc xi yi yi >=>
                                 cong (_i* yi) (i*-commute xi yi) >=>
                                 sym (i*-assoc yi xi yi)) >=>
                  i*-assoc xi yi (xi i* yi)
      xy-split : xy == sxy * sxy
      xy-split = sym (sqrt² xy 0≤xy)

      imb-xiyi = i*-preserves-ImbalancedI xi yi imb-xi imb-yi

      xy∈1 : ℝ∈Iℚ xy ((xi i* xi) i* (yi i* yi))
      xy∈1 = ℝ∈Iℚ-* x y (xi i* xi) (yi i* yi) x∈xixi y∈yiyi
      xy∈2 : ℝ∈Iℚ (sxy * sxy) ((xi i* yi) i* (xi i* yi))
      xy∈2 = subst2 ℝ∈Iℚ xy-split xiyi-swap xy∈1


    ℝ∈Iℚ-sqrt-*-split : (xi yi : Iℚ) -> ℝ∈Iℚ sx xi -> ℝ∈Iℚ sy yi -> ℝ∈Iℚ sxy (xi i* yi)
    ℝ∈Iℚ-sqrt-*-split xi yi sx∈xi sy∈yi =
      handle (ℝ∈Iℚ-≤0-ΣImbalancedI sx xi 0≤sx sx∈xi) (ℝ∈Iℚ-≤0-ΣImbalancedI sy yi 0≤sy sy∈yi)
      where
      handle : Σ[ ai ∈ Iℚ ] (ℝ∈Iℚ sx ai × ImbalancedI ai × ai i⊆ xi) ->
               Σ[ bi ∈ Iℚ ] (ℝ∈Iℚ sy bi × ImbalancedI bi × bi i⊆ yi) ->
               ℝ∈Iℚ sxy (xi i* yi)
      handle (ai , sx∈ai , imb-ai , ai⊆xi) (bi , sy∈bi , imb-bi , bi⊆yi) =
        ℝ∈Iℚ-⊆ sxy (i*-preserves-⊆ ai⊆xi bi⊆yi)
          (ℝ∈Iℚ-sqrt-*-ImbalancedI ai bi sx∈ai sy∈bi imb-ai imb-bi)

    ℝ∈Iℚ-sqrt-* : (ai : Iℚ) -> ℝ∈Iℚ sxsy ai -> ℝ∈Iℚ sxy ai
    ℝ∈Iℚ-sqrt-* ai sxsy∈ai = unsquash (isProp-ℝ∈Iℚ sxy ai) (∥-map handle (ℝ∈Iℚ-*⁻ sx sy ai sxsy∈ai))
      where
      handle : Σ[ bi ∈ Iℚ ] Σ[ ci ∈ Iℚ ] (ℝ∈Iℚ sx bi × ℝ∈Iℚ sy ci × (bi i* ci) i⊆ ai) -> ℝ∈Iℚ sxy ai
      handle (bi , ci , sx∈bi , sy∈ci , bici⊆ai) =
        ℝ∈Iℚ-⊆ sxy bici⊆ai (ℝ∈Iℚ-sqrt-*-split bi ci sx∈bi sy∈ci)

  sqrt-* : sxy == sxsy
  sqrt-* = sym (ℝ∈Iℚ->path sxsy sxy ℝ∈Iℚ-sqrt-*)
