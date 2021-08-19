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
open import rational
open import rational.proper-interval.abs
open import rational.proper-interval
open import rational.order
open import rational.minmax
open import rational.squares
open import real
open import real.arithmetic
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
open import truncation


module _ (x : ℝ) (x≮0 : x ≮ 0ℝ)
  where
  private
    module x = Real x

    U : Pred ℚ ℓ-zero
    U q = (0r ≤ q) × (x.U (q * q))

    L : Pred ℚ ℓ-zero
    L q = (Neg q) ⊎ ((0r ≤ q) × (x.L (q * q)))

    isProp-U : isPropValuedPred U
    isProp-U q = isProp× (isProp-≤ 0r q) (x.isProp-U (q * q))

    isProp-L : isPropValuedPred L
    isProp-L q = isProp⊎ (isProp-Neg q) (isProp× (isProp-≤ 0r q) (x.isProp-L (q * q)))
                 (\n (0≤q , _) -> (NonNeg->¬Neg (0≤-NonNeg q 0≤q) n))

    disjoint : Universal (Comp (L ∩ U))
    disjoint q (inj-l nq , (0≤q , _)) = (NonNeg->¬Neg (0≤-NonNeg q 0≤q) nq)
    disjoint q (inj-r (_ , lqq) , (_ , uqq)) = x.disjoint (q * q) (lqq , uqq)

    Inhabited-L : Inhabited L
    Inhabited-L = ∣ (- 1r) , (inj-l (minus-flips-0< 0<1r)) ∣

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map handle x.Inhabited-U
      where
      handle : Σ ℚ x.U -> Σ ℚ U
      handle (q , xu-q) = handle2 (split-< q 1r)
        where
        handle2 : (q < 1r ⊎ 1r ≤ q) -> Σ ℚ U
        handle2 (inj-l q<1) = 1r , (weaken-< 0<1r , x.isUpperSet-U q _ q<1*1 xu-q)
          where
          q<1*1 = subst (q <_) (sym *-right-one) q<1
        handle2 (inj-r 1≤q) = q , (0≤q , (isUpperSet≤ x q _ q<q*q xu-q))
          where
          0≤q = trans-≤ (weaken-< 0<1r) 1≤q
          q<q*q = subst (_≤ (q * q)) *-right-one (*₁-preserves-≤ q 1r q 0≤q 1≤q)

    isUpperSet-U : isUpperSet U
    isUpperSet-U q r q<r (0≤q , xu-qq) =
      (weaken-< 0<r , x.isUpperSet-U (q * q) (r * r) qq<rr xu-qq)
      where
      0<r = trans-≤-< 0≤q q<r
      qq<rr : (q * q) < (r * r)
      qq<rr = trans-≤-< (*₁-preserves-≤ q q r 0≤q (weaken-< q<r)) (*₂-preserves-< q r r q<r 0<r)

    isLowerSet-L : isLowerSet L
    isLowerSet-L q r q<r (inj-l r<0) = (inj-l (trans-< q<r r<0))
    isLowerSet-L q r q<r (inj-r (0≤r , xu-rr)) = handle (split-< q 0r)
      where
      handle : (q < 0r ⊎ 0r ≤ q) -> L q
      handle (inj-l q<0) = (inj-l q<0)
      handle (inj-r 0≤q) = (inj-r (0≤q , isLowerSet≤ x (q * q) (r * r) qq≤rr xu-rr))
        where
        q≤r = weaken-< q<r
        qq≤rr : (q * q) ≤ (r * r)
        qq≤rr = trans-≤ (*₁-preserves-≤ q q r 0≤q q≤r) (*₂-preserves-≤ q r r q≤r 0≤r)


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q (0≤q , xu-qq) = ∥-bind handle (x.isLowerOpen-U qq xu-qq)
      where
      qq = (q * q)
      handle : Σ[ r ∈ ℚ ] (r < qq × x.U r) -> ∃[ r ∈ ℚ ] (r < q × U r)
      handle (r , (r<qq , xu-r)) = handle2 (split-< 0r r)
        where
        handle2 : (0r < r ⊎ r ≤ 0r) -> ∃[ r ∈ ℚ ] (r < q × U r)
        handle2 (inj-r r≤0) = bot-elim (x≮0 x<0)
          where
          handle3 : Σ[ s ∈ ℚ ] (s < r × x.U s) -> x ℝ<' 0ℝ
          handle3 (s , s<r , xu-s) = (s , xu-s , trans-<-≤ s<r r≤0)

          x<0 : x < 0ℝ
          x<0 = ∥-map handle3 (x.isLowerOpen-U r xu-r)
        handle2 (inj-l 0<r) = ∥-map handle3 (squares-dense-upper-square 0<r 0≤q r<qq)
          where
          handle3 : _ -> Σ[ r ∈ ℚ ] (r < q × U r)
          handle3 (s , (t , 0≤t , tt=s) , r<s , s<qq) =
            t , (squares-ordered 0≤t 0≤q tt<qq)
              , 0≤t , subst x.U (sym tt=s) (x.isUpperSet-U r s r<s xu-r)
            where
            tt<qq : (t * t) < (q * q)
            tt<qq = subst (_< (q * q)) (sym tt=s) s<qq

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q (inj-l q<0) = ∣ 1/2r * q , q<1/2q , inj-l 1/2q<0 ∣
      where
      q<1/2q = subst2 _<_ *-left-one refl (*₂-flips-< 1/2r 1r q 1/2r<1r q<0)
      1/2q<0 = subst2 _<_ refl *-right-zero (*₁-preserves-< 1/2r q 0r Pos-1/2r q<0)

    isUpperOpen-L q (inj-r (0≤q , xl-qq)) = ∥-bind handle (x.isUpperOpen-L qq xl-qq)
      where
      qq = (q * q)
      handle : Σ[ r ∈ ℚ ] (qq < r × x.L r) -> ∃[ r ∈ ℚ ] (q < r × L r)
      handle (r , (qq<r , xl-r)) = ∥-map handle2 (squares-dense-lower-square 0≤q qq<r)
        where
        0≤qq : 0r ≤ qq
        0≤qq = *-preserves-0≤ _ _ 0≤q 0≤q

        handle2 : _ -> Σ[ r ∈ ℚ ] (q < r × L r)
        handle2 (s , (t , 0≤t , tt=s) , qq<s , s<r) =
          t , (squares-ordered 0≤q 0≤t (subst2 _<_ refl (sym tt=s) qq<s)) ,
          inj-r (0≤t , subst x.L (sym tt=s) (x.isLowerSet-L s r s<r xl-r))

    located : (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located q r q<r = handle (split-< q 0r)
      where
      handle : (q < 0r ⊎ 0r ≤ q) -> ∥ L q ⊎ U r ∥
      handle (inj-l q<0) = ∣ inj-l (inj-l q<0) ∣
      handle (inj-r 0≤q) = ∥-map handle2 (x.located qq rr qq<rr)
        where
        qq = (q * q)
        rr = (r * r)

        0<r = trans-≤-< 0≤q q<r
        0≤r = weaken-< 0<r

        qq<rr : qq < rr
        qq<rr = squares-ordered⁺ 0≤q q<r

        handle2 : x.L qq ⊎ x.U rr -> L q ⊎ U r
        handle2 (inj-l xl-qq) = inj-l (inj-r (0≤q , xl-qq))
        handle2 (inj-r xu-rr) = inj-r (0≤r , xu-rr)

  sqrtℝᵉ : ℝ
  sqrtℝᵉ = record
    { L = L
    ; U = U
    ; isProp-L = isProp-L
    ; isProp-U = isProp-U
    ; Inhabited-L = Inhabited-L
    ; Inhabited-U = Inhabited-U
    ; isLowerSet-L = isLowerSet-L
    ; isUpperSet-U = isUpperSet-U
    ; isUpperOpen-L = isUpperOpen-L
    ; isLowerOpen-U = isLowerOpen-U
    ; disjoint = disjoint
    ; located = located
    }

  abstract
    sqrtℝ : ℝ
    sqrtℝ = sqrtℝᵉ

    sqrtℝ-eval : sqrtℝ == sqrtℝᵉ
    sqrtℝ-eval = refl

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


module _ (x : ℝ) (x≮0 : x ≮ 0ℝ) where
  private
    sx = (sqrtℝᵉ x x≮0)
    sxsx = sx ℝ*ᵉ sx
    module x = Real x
    module sx = Real sx
    module sxsx = Real sxsx

    ℝ∈Iℚ-sqrt⁻ : (xi yi : Iℚ) -> ℝ∈Iℚ sx xi -> ℝ∈Iℚ sx yi -> ℝ∈Iℚ x (xi i* yi)
    ℝ∈Iℚ-sqrt⁻ xi@(Iℚ-cons xl xu xl≤xu) yi@(Iℚ-cons yl yu yl≤yu)
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
          x∈xyi = ℝ∈Iℚ-sqrt⁻ xi yi sx∈xi sx∈yi

          zwi = zi i* wi
          x∈zwi : ℝ∈Iℚ x (zi i* wi)
          x∈zwi = ℝ∈Iℚ-sqrt⁻ zi wi sx∈zi sx∈wi

  abstract
    *-sqrt : (sqrtℝ x x≮0) * (sqrtℝ x x≮0) == x
    *-sqrt = cong2 _ℝ*_ (sqrtℝ-eval x x≮0) (sqrtℝ-eval x x≮0) >=>
             ℝ*-eval {sx} {sx} >=>
             *-sqrtᵉ

private
  module _ (x : ℝ) where
    private
      xx = x ℝ*ᵉ x
      module x = Real x
      module xx = Real xx

    ≮0-squareᵉ : xx ≮ 0ℝ
    ≮0-squareᵉ x²<0 = unsquash isPropBot (∥-bind handle x²<0)
      where
      handle : Σ[ q ∈ ℚ ] (xx.U q × q < 0r) -> ∥ Bot ∥
      handle (q , xxU-q , q<0) = ∥-map handle2 xxU-q
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
          uu<0 = trans-≤-< (trans-≤ (snd uu∈ai*bi) abi≤q) q<0

abstract
  ≮0-square : (x : ℝ) -> (x * x) ≮ 0ℝ
  ≮0-square x = subst (_≮ 0ℝ) (sym (ℝ*-eval {x} {x})) (≮0-squareᵉ x)

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
    sqrt-* : sqrtℝ (x * x) (≮0-square x) == absℝ x
    sqrt-* = sqrtℝ-eval (x * x) (≮0-square x) >=>
             cong2-dep sqrtℝᵉ (ℝ*-eval {x} {x})
                              (isProp->PathP (\_ -> (isProp¬ _)) (≮0-square x) (≮0-squareᵉ x)) >=>
             sqrt-*ᵉ (≮0-squareᵉ x)
