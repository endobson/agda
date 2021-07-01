{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication where

open import base
open import equality
open import isomorphism
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.factor-order
open import rational.minmax
open import rational.proper-interval
open import rational.proper-interval.maxabs-multiplication
open import rational.proper-interval.multiplication-strict-cross-zero
open import real
open import real.sequence
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation
open import univalence

ℝ∈Iℚ : ℝ -> Iℚ -> Type₀
ℝ∈Iℚ z (Iℚ-cons l u _) = Real.L z l × Real.U z u

ℝ∈Iℚ->Overlap : (z : ℝ) (a b : Iℚ) -> ℝ∈Iℚ z a -> ℝ∈Iℚ z b -> Overlap a b
ℝ∈Iℚ->Overlap z a b (al , au) (bl , bu) =
  inj-l (ℝ-bounds->ℚ< z _ _ bl au) , inj-l (ℝ-bounds->ℚ< z _ _ al bu)

ℝ∈Iℚ-intersect : (z : ℝ) (a b : Iℚ) -> (ea : ℝ∈Iℚ z a) -> (eb : ℝ∈Iℚ z b) ->
                 ℝ∈Iℚ z (i-intersect a b (ℝ∈Iℚ->Overlap z a b ea eb))
ℝ∈Iℚ-intersect z a b (al , au) (bl , bu) =
  maxℚ-property {P = Real.L z} _ _ al bl ,
  minℚ-property {P = Real.U z} _ _ au bu

ℝ∈Iℚ->¬Constant : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z a -> ¬ (ConstantI a)
ℝ∈Iℚ->¬Constant z a (al , au) p =
  Real.disjoint z (Iℚ.u a) (subst (Real.L z) p al , au)

ℝ∈Iℚ->NonConstant : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z a -> NonConstantI a
ℝ∈Iℚ->NonConstant z a (al , au) = (ℝ-bounds->ℚ< z _ _ al au)

isProp-ℝ∈Iℚ : (z : ℝ) (a : Iℚ) -> isProp (ℝ∈Iℚ z a)
isProp-ℝ∈Iℚ z (Iℚ-cons l u _) = isProp× (Real.isProp-L z l) (Real.isProp-U z u)

private
  module _ (x y : ℝ) where
    L' : Pred ℚ ℓ-zero
    L' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Lower (xi i* yi) q)

    U' : Pred ℚ ℓ-zero
    U' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Upper (xi i* yi) q)

module _ (x y : ℝ)
  where
  private
    module x = Real x
    module y = Real y

    L : Pred ℚ ℓ-zero
    L q = ∥ L' x y q ∥
    U : Pred ℚ ℓ-zero
    U q = ∥ U' x y q ∥

    NonZero-UpperOpen : (z : ℝ) (q : ℚ) (l : Real.L z q) -> ∃[ r ∈ ℚ ] (NonZero r × q < r × Real.L z r)
    NonZero-UpperOpen z q lq = ∥-bind handle (Real.isUpperOpen-L z q lq)
      where
      Ans = ∃[ r ∈ ℚ ] (NonZero r × q < r × Real.L z r)
      handle : Σ[ r ∈ ℚ ] (q < r × Real.L z r) -> Ans
      handle (r , q<r , lr) = handle2 _ (isSign-self r)
        where
        handle2 : (s : Sign) -> (isSign s r) -> Ans
        handle2 pos-sign pr = ∣ r , inj-l pr , q<r , lr ∣
        handle2 neg-sign nr = ∣ r , inj-r nr , q<r , lr ∣
        handle2 zero-sign zr = ∥-bind handle3 (Real.isUpperOpen-L z r lr)
          where
          handle3 : Σ[ r2 ∈ ℚ ] (r < r2 × Real.L z r2) -> Ans
          handle3 (r2 , r<r2 , lr2) = ∣ r2 , inj-l pr2 , trans-< {_} {_} {_} {q} {r} {r2} q<r r<r2 , lr2 ∣
            where
            pr2 : Pos r2
            pr2 = 0<-Pos r2 (subst (_< r2) (Zero-path r zr) r<r2)

    NonZero-LowerOpen : (z : ℝ) (q : ℚ) (l : Real.U z q) -> ∃[ r ∈ ℚ ] (NonZero r × r < q × Real.U z r)
    NonZero-LowerOpen z q uq = ∥-bind handle (Real.isLowerOpen-U z q uq)
      where
      Ans = ∃[ r ∈ ℚ ] (NonZero r × r < q × Real.U z r)
      handle : Σ[ r ∈ ℚ ] (r < q × Real.U z r) -> Ans
      handle (r , r<q , ur) = handle2 _ (isSign-self r)
        where
        handle2 : (s : Sign) -> (isSign s r) -> Ans
        handle2 pos-sign pr = ∣ r , inj-l pr , r<q , ur ∣
        handle2 neg-sign nr = ∣ r , inj-r nr , r<q , ur ∣
        handle2 zero-sign zr = ∥-bind handle3 (Real.isLowerOpen-U z r ur)
          where
          handle3 : Σ[ r2 ∈ ℚ ] (r2 < r × Real.U z r2) -> Ans
          handle3 (r2 , r2<r , ur2) = ∣ r2 , inj-r nr2 , trans-< {_} {_} {_} {r2} {r} {q} r2<r r<q , ur2 ∣
            where
            nr2 : Neg r2
            nr2 = <0-Neg r2 (subst (r2 <_) (Zero-path r zr) r2<r)

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-map4 handle x.Inhabited-L x.Inhabited-U y.Inhabited-L y.Inhabited-U
      where
      handle : Σ ℚ x.L -> Σ ℚ x.U -> Σ ℚ y.L -> Σ ℚ y.U -> Σ ℚ L
      handle (a , la) (b , ub) (c , lc) (d , ud) =
        q , ∣ ab , cd , (la , ub) , (lc , ud) , refl-ℚ≤ {q} ∣
        where
        ab : Iℚ
        ab = Iℚ-cons a b (inj-l (ℝ-bounds->ℚ< x _ _ la ub))
        cd : Iℚ
        cd = Iℚ-cons c d (inj-l (ℝ-bounds->ℚ< y _ _ lc ud))
        q = Iℚ.l (ab i* cd)

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map4 handle x.Inhabited-L x.Inhabited-U y.Inhabited-L y.Inhabited-U
      where
      handle : Σ ℚ x.L -> Σ ℚ x.U -> Σ ℚ y.L -> Σ ℚ y.U -> Σ ℚ U
      handle (a , la) (b , ub) (c , lc) (d , ud) =
        q , ∣ ab , cd , (la , ub) , (lc , ud) , refl-ℚ≤ {q} ∣
        where
        ab : Iℚ
        ab = Iℚ-cons a b (inj-l (ℝ-bounds->ℚ< x _ _ la ub))
        cd : Iℚ
        cd = Iℚ-cons c d (inj-l (ℝ-bounds->ℚ< y _ _ lc ud))
        q = Iℚ.u (ab i* cd)

    isLowerSet-L : isLowerSet L
    isLowerSet-L a b a<b = ∥-map handle
      where
      handle : L' x y b -> L' x y a
      handle (xi , yi , exi , eyi , lt) =
        (xi , yi , exi , eyi , inj-l (trans-<-≤ {a} {b} {Iℚ.l (xi i* yi)} a<b lt))

    isUpperSet-U : isUpperSet U
    isUpperSet-U a b a<b = ∥-map handle
      where
      handle : U' x y a -> U' x y b
      handle (xi , yi , exi , eyi , lt) =
        (xi , yi , exi , eyi , inj-l (trans-≤-< {Iℚ.u (xi i* yi)} {a} {b} lt a<b))


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' x y q -> ∃[ r ∈ ℚ ] (q < r × L r)
      handle (xi@(Iℚ-cons a b _) , yi@(Iℚ-cons c d _) , (xl , xu) , (yl , yu) , lt) =
        ∥-map4 handle2 (NonZero-UpperOpen x _ xl) (NonZero-LowerOpen x _ xu)
                       (y.isUpperOpen-L _ yl) (y.isLowerOpen-U _ yu)
        where
        handle2 : Σ[ a' ∈ ℚ ] (NonZero a' × a < a' × x.L a') ->
                  Σ[ b' ∈ ℚ ] (NonZero b' × b' < b × x.U b') ->
                  Σ[ c' ∈ ℚ ] (c < c' × y.L c') ->
                  Σ[ d' ∈ ℚ ] (d' < d × y.U d') -> _
        handle2 (a' , nza' , a<a' , la') (b' , nzb' , b'<b , ub') (c' , c<c' , lc') (d' , d'<d , ud') =
          r , q<r , ∣ xi' , yi' , (la' , ub') , (lc' , ud') , refl-ℚ≤ {r} ∣
          where
          xi' = Iℚ-cons a' b' (inj-l (ℝ-bounds->ℚ< x a' b' la' ub'))
          yi' = Iℚ-cons c' d' (inj-l (ℝ-bounds->ℚ< y c' d' lc' ud'))
          r = Iℚ.l (xi' i* yi')

          nz-xi' : ¬ (ZeroEndedI xi')
          nz-xi' (inj-l za') = NonZero->¬Zero nza' za'
          nz-xi' (inj-r zb') = NonZero->¬Zero nzb' zb'

          p'⊂p : (xi' i* yi') i⊂ (xi i* yi)
          p'⊂p = i*-preserves-⊂ {xi'} {xi} {yi'} {yi} (i⊂-cons a<a' b'<b) (i⊂-cons c<c' d'<d) nz-xi'

          q<r : q < r
          q<r = trans-≤-< {q} {Iℚ.l (xi i* yi)} {r} lt (_i⊂_.l p'⊂p)

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-bind handle
      where
      handle : U' x y q -> ∃[ r ∈ ℚ ] (r < q × U r)
      handle (xi@(Iℚ-cons a b _) , yi@(Iℚ-cons c d _) , (xl , xu) , (yl , yu) , lt) =
        ∥-map4 handle2 (NonZero-UpperOpen x _ xl) (NonZero-LowerOpen x _ xu)
                       (y.isUpperOpen-L _ yl) (y.isLowerOpen-U _ yu)
        where
        handle2 : Σ[ a' ∈ ℚ ] (NonZero a' × a < a' × x.L a') ->
                  Σ[ b' ∈ ℚ ] (NonZero b' × b' < b × x.U b') ->
                  Σ[ c' ∈ ℚ ] (c < c' × y.L c') ->
                  Σ[ d' ∈ ℚ ] (d' < d × y.U d') -> _
        handle2 (a' , nza' , a<a' , la') (b' , nzb' , b'<b , ub') (c' , c<c' , lc') (d' , d'<d , ud') =
          r , r<q , ∣ xi' , yi' , (la' , ub') , (lc' , ud') , refl-ℚ≤ {r} ∣
          where
          xi' = Iℚ-cons a' b' (inj-l (ℝ-bounds->ℚ< x a' b' la' ub'))
          yi' = Iℚ-cons c' d' (inj-l (ℝ-bounds->ℚ< y c' d' lc' ud'))
          r = Iℚ.u (xi' i* yi')

          nz-xi' : ¬ (ZeroEndedI xi')
          nz-xi' (inj-l za') = NonZero->¬Zero nza' za'
          nz-xi' (inj-r zb') = NonZero->¬Zero nzb' zb'

          p'⊂p : (xi' i* yi') i⊂ (xi i* yi)
          p'⊂p = i*-preserves-⊂ {xi'} {xi} {yi'} {yi} (i⊂-cons a<a' b'<b) (i⊂-cons c<c' d'<d) nz-xi'

          r<q : r < q
          r<q = trans-<-≤ {r} {Iℚ.u (xi i* yi)} {q} (_i⊂_.u p'⊂p) lt



    disjoint : Universal (Comp (L ∩ U))
    disjoint q (lq , uq) = unsquash isPropBot (∥-map2 handle lq uq)
      where
      handle : L' x y q -> U' x y q -> Bot
      handle (xi1 , yi1 , exi1 , eyi1 , l1) (xi2 , yi2 , exi2 , eyi2 , u2) =
        handle2 (i*-Constant xi3 yi3 Constant-p3)
        where
        xi3 : Iℚ
        xi3 = i-intersect xi1 xi2 (ℝ∈Iℚ->Overlap x xi1 xi2 exi1 exi2)

        yi3 : Iℚ
        yi3 = i-intersect yi1 yi2 (ℝ∈Iℚ->Overlap y yi1 yi2 eyi1 eyi2)

        xi3⊆xi1 : xi3 i⊆ xi1
        xi3⊆xi1 = i-intersect-⊆₁ _ _ _
        xi3⊆xi2 : xi3 i⊆ xi2
        xi3⊆xi2 = i-intersect-⊆₂ _ _ _
        yi3⊆yi1 : yi3 i⊆ yi1
        yi3⊆yi1 = i-intersect-⊆₁ _ _ _
        yi3⊆yi2 : yi3 i⊆ yi2
        yi3⊆yi2 = i-intersect-⊆₂ _ _ _

        p1 = xi1 i* yi1
        p2 = xi2 i* yi2
        p3 = xi3 i* yi3

        p3⊆p1 : p3 i⊆ p1
        p3⊆p1 = trans-i⊆ (i*₁-preserves-⊆ xi3 yi3⊆yi1) (i*₂-preserves-⊆ xi3⊆xi1 yi1)
        p3⊆p2 : p3 i⊆ p2
        p3⊆p2 = trans-i⊆ (i*₁-preserves-⊆ xi3 yi3⊆yi2) (i*₂-preserves-⊆ xi3⊆xi2 yi2)

        l3 : i-Lower p3 q
        l3 = i⊆-Lower p3⊆p1 q l1

        u3 : i-Upper p3 q
        u3 = i⊆-Upper p3⊆p2 q u2

        Constant-p3 : ConstantI p3
        Constant-p3 = LowerUpper->Constant {q} p3 l3 u3

        handle2 : ConstantI xi3 ⊎ ConstantI yi3 -> Bot
        handle2 (inj-l cx3) = ℝ∈Iℚ->¬Constant x xi3 (ℝ∈Iℚ-intersect x xi1 xi2 exi1 exi2) cx3
        handle2 (inj-r cy3) = ℝ∈Iℚ->¬Constant y yi3 (ℝ∈Iℚ-intersect y yi1 yi2 eyi1 eyi2) cy3

    located : (a b : ℚ) -> a < b -> ∥ L a ⊎ U b ∥
    located a b a<b = ∥-bind4 initial-bound x.Inhabited-L x.Inhabited-U y.Inhabited-L y.Inhabited-U
      where
      Ans = ∥ L a ⊎ U b ∥
      d = diffℚ a b

      initial-bound : Σ ℚ x.L -> Σ ℚ x.U -> Σ ℚ y.L -> Σ ℚ y.U -> Ans
      initial-bound (xb1' , xbl') (xb2' , xbu') (yb1' , ybl') (yb2' , ybu') =
        ∥-bind2 handle (find-open-ball x ε⁺) (find-open-ball y ε⁺)
        where

        xi' : Iℚ
        xi' = Iℚ-cons xb1' xb2' (inj-l (ℝ-bounds->ℚ< x _ _ xbl' xbu'))
        yi' : Iℚ
        yi' = Iℚ-cons yb1' yb2' (inj-l (ℝ-bounds->ℚ< y _ _ ybl' ybu'))

        m-xi' = i-maxabs xi'
        m-yi' = i-maxabs yi'

        exi' : ℝ∈Iℚ x xi'
        exi' = xbl' , xbu'

        eyi' : ℝ∈Iℚ y yi'
        eyi' = ybl' , ybu'

        pos-m-xi' : Pos m-xi'
        pos-m-xi' = handle (NonNeg-i-maxabs xi')
          where
          handle : NonNeg m-xi' -> Pos m-xi'
          handle (inj-l p) = p
          handle (inj-r z) = bot-elim (x.disjoint 0r (subst x.L (cong Iℚ.l zp) xbl' ,
                                                      subst x.U (cong Iℚ.u zp) xbu'))
            where
            zp = i-maxabs-Zero xi' z

        pos-m-yi' : Pos m-yi'
        pos-m-yi' = handle (NonNeg-i-maxabs yi')
          where
          handle : NonNeg m-yi' -> Pos m-yi'
          handle (inj-l p) = p
          handle (inj-r z) = bot-elim (y.disjoint 0r (subst y.L (cong Iℚ.l zp) ybl' ,
                                                      subst y.U (cong Iℚ.u zp) ybu'))
            where
            zp = i-maxabs-Zero yi' z


        sm = (m-yi' r+ m-xi')
        pos-sm = r+-preserves-Pos _ _ pos-m-yi' pos-m-xi'

        nn-sm = r+-NonNeg-NonNeg

        sm-inv : ℚInv sm
        sm-inv z-sm =
          NonPos->¬Pos (inj-r (subst Zero (sym z-sm) Zero-0r)) pos-sm

        ε = (d r* (r1/ sm sm-inv))

        ε⁺ : ℚ⁺
        ε⁺ = ε , (r*₁-preserves-sign (d , a<b) _ (r1/-preserves-Pos sm sm-inv pos-sm))

        ε-path : (ε r* (m-yi' r+ m-xi')) == d
        ε-path = r*-assoc _ _ _ >=>
                 (cong (d r*_) (r1/-inverse sm sm-inv)) >=>
                 (r*-right-one d)



        handle : OpenBall x ε  -> OpenBall y ε -> Ans
        handle (xb1 , xb2 , xbl , xbu , xbe) (yb1 , yb2 , ybl , ybu , ybe) =
          handle2 (split-< a l)
          where
          xi : Iℚ
          xi = Iℚ-cons xb1 xb2 (inj-l (ℝ-bounds->ℚ< x _ _ xbl xbu))
          yi : Iℚ
          yi = Iℚ-cons yb1 yb2 (inj-l (ℝ-bounds->ℚ< y _ _ ybl ybu))

          exi : ℝ∈Iℚ x xi
          exi = xbl , xbu
          eyi : ℝ∈Iℚ y yi
          eyi = ybl , ybu

          oxi : Overlap xi' xi
          oxi = ℝ∈Iℚ->Overlap x xi' xi exi' exi
          oyi : Overlap yi' yi
          oyi = ℝ∈Iℚ->Overlap y yi' yi eyi' eyi

          mxi : Iℚ
          mxi = i-intersect xi' xi oxi
          myi : Iℚ
          myi = i-intersect yi' yi oyi

          emxi : ℝ∈Iℚ x mxi
          emxi = ℝ∈Iℚ-intersect x xi' xi exi' exi
          emyi : ℝ∈Iℚ y myi
          emyi = ℝ∈Iℚ-intersect y yi' yi eyi' eyi

          mxi⊆xi' = i-intersect-⊆₁ xi' xi oxi
          myi⊆yi' = i-intersect-⊆₁ yi' yi oyi
          mxi⊆xi  = i-intersect-⊆₂ xi' xi oxi
          myi⊆yi  = i-intersect-⊆₂ yi' yi oyi

          w-mxi = i-width mxi
          w-myi = i-width myi
          m-mxi = i-maxabs mxi
          m-myi = i-maxabs myi

          nn-w-mxi = NonNeg-i-width mxi
          nn-w-myi = NonNeg-i-width myi

          nn-m-xi' = NonNeg-i-maxabs xi'
          nn-m-yi' = NonNeg-i-maxabs yi'

          w-xi = i-width xi
          w-yi = i-width yi

          w-mxi≤w-xi  = i-width-⊆ mxi⊆xi
          w-myi≤w-yi  = i-width-⊆ myi⊆yi
          m-mxi≤m-xi' = i-maxabs-⊆ mxi⊆xi'
          m-myi≤m-yi' = i-maxabs-⊆ myi⊆yi'

          w-mxi≤ε  = subst (w-mxi ℚ≤_) xbe w-mxi≤w-xi
          w-myi≤ε  = subst (w-myi ℚ≤_) ybe w-myi≤w-yi

          wm-xy-≤ : (w-mxi r* m-myi) ℚ≤ (ε r* m-yi')
          wm-xy-≤ = trans-ℚ≤ {(w-mxi r* m-myi)} {(w-mxi r* m-yi')} {(ε r* m-yi')}
                             (r*₁-preserves-≤ (w-mxi , nn-w-mxi) m-myi m-yi' m-myi≤m-yi')
                             (r*₂-preserves-≤ w-mxi ε (m-yi' , nn-m-yi') w-mxi≤ε)

          mw-xy-≤ : (m-mxi r* w-myi) ℚ≤ (ε r* m-xi')
          mw-xy-≤ = trans-ℚ≤ {(m-mxi r* w-myi)} {(m-xi' r* w-myi)} {(ε r* m-xi')}
                             (r*₂-preserves-≤ m-mxi m-xi' (w-myi , nn-w-myi)  m-mxi≤m-xi')
                             (subst ((m-xi' r* w-myi) ℚ≤_) (r*-commute m-xi' ε)
                                    (r*₁-preserves-≤ (m-xi' , nn-m-xi') w-myi ε w-myi≤ε))

          wmmw = ((w-mxi r* m-myi) r+ (m-mxi r* w-myi))
          wmmw≤d : wmmw ℚ≤ d
          wmmw≤d =
            subst (wmmw ℚ≤_) (sym (RationalSemiring.*-distrib-+-left {ε} {m-yi'} {m-xi'}) >=>
                              ε-path)
                  (r+-both-preserves-≤ (w-mxi r* m-myi) (ε r* m-yi') (m-mxi r* w-myi) (ε r* m-xi')
                                       wm-xy-≤ mw-xy-≤)


          p = mxi i* myi
          l = Iℚ.l p
          u = Iℚ.u p
          w = i-width p

          w≤wmmw : w ℚ≤ wmmw
          w≤wmmw = i*-width-≤ mxi myi

          w≤d : w ℚ≤ d
          w≤d = trans-ℚ≤ {w} {wmmw} {d} w≤wmmw wmmw≤d

          handle2 : (a < l ⊎ l ℚ≤ a) -> Ans
          handle2 (inj-l a<l) = ∣ inj-l ∣ (mxi , myi , emxi , emyi , (inj-l a<l)) ∣ ∣
          handle2 (inj-r l≤a) = ∣ inj-r ∣ (mxi , myi , emxi , emyi , u≤b) ∣ ∣
            where
            u≤b : u ℚ≤ b
            u≤b = subst2 _ℚ≤_ (diffℚ-step l u) (diffℚ-step a b) (r+-both-preserves-≤ l a w d l≤a w≤d)

  _ℝ*_ : ℝ
  _ℝ*_ = record
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




module _ (x y : ℝ) where
  private
    module x = Real x
    module y = Real y
    xy = x ℝ* y
    yx = y ℝ* x
    module xy = Real xy
    module yx = Real yx

    L-path : (q : ℚ) -> xy.L q == yx.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (xy.L q) (yx.L q)
      i .fun = ∥-map handle
        where
        handle : L' x y q -> L' y x q
        handle (a , b , ea , eb , l) =
          b , a , eb , ea , subst (\x -> i-Lower x q) (i*-commute a b) l
      i .inv = ∥-map handle
        where
        handle : L' y x q -> L' x y q
        handle (a , b , ea , eb , l) =
          b , a , eb , ea , subst (\x -> i-Lower x q) (i*-commute a b) l
      i .rightInv _ = squash _ _
      i .leftInv _ = squash _ _

    U-path : (q : ℚ) -> xy.U q == yx.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (xy.U q) (yx.U q)
      i .fun = ∥-map handle
        where
        handle : U' x y q -> U' y x q
        handle (a , b , ea , eb , l) =
          b , a , eb , ea , subst (\x -> i-Upper x q) (i*-commute a b) l
      i .inv = ∥-map handle
        where
        handle : U' y x q -> U' x y q
        handle (a , b , ea , eb , l) =
          b , a , eb , ea , subst (\x -> i-Upper x q) (i*-commute a b) l
      i .rightInv _ = squash _ _
      i .leftInv _ = squash _ _

  ℝ*-commute : xy == yx
  ℝ*-commute = LU-paths->path xy yx L-path U-path


module _ (x : ℝ)
  where
  private
    module x = Real x
    module 1ℝ = Real 1ℝ
    1x = 1ℝ ℝ* x
    module 1x = Real 1x

    isLowerSet≤ : (q r : ℚ) -> (q ℚ≤ r) -> x.L r -> x.L q
    isLowerSet≤ q r q≤r lr = unsquash (x.isProp-L q) (∥-map handle (x.isUpperOpen-L r lr))
      where
      handle : Σ[ s ∈ ℚ ] (r < s × x.L s) -> x.L q
      handle (s , r<s , ls) = x.isLowerSet-L q s (trans-≤-< {q} {r} {s} q≤r r<s) ls

    isUpperSet≤ : (q r : ℚ) -> (q ℚ≤ r) -> x.U q -> x.U r
    isUpperSet≤ q r q≤r uq = unsquash (x.isProp-U r) (∥-map handle (x.isLowerOpen-U q uq))
      where
      handle : Σ[ s ∈ ℚ ] (s < q × x.U s) -> x.U r
      handle (s , s<q , us) = x.isUpperSet-U s r (trans-<-≤ {s} {q} {r} s<q q≤r) us

    L-path : (q : ℚ) -> 1x.L q == x.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (1x.L q) (x.L q)
      i .rightInv _ = x.isProp-L q _ _
      i .leftInv _ = 1x.isProp-L q _ _
      i .inv xl-q = ∥-bind2 handle x.Inhabited-U (x.isUpperOpen-L q xl-q)
         where
         handle : Σ ℚ x.U -> Σ[ r ∈ ℚ ] (q < r × x.L r) -> 1x.L q
         handle (s , xu-s) (r , q<r , xl-r) =
           handle2 (find-shrink-factor rs⊂qs') (find-growth-factor rs⊂qs')
           where

           s' : ℚ
           s' = 1r r+ s

           s<s' : s < s'
           s<s' = subst Pos (sym (r+-right-zero 1r) >=>
                             cong (1r r+_) (sym (r+-inverse s)) >=>
                             sym (r+-assoc 1r s (r- s))) Pos-1r

           r<s : r < s
           r<s = (ℝ-bounds->ℚ< x _ _ xl-r xu-s)

           q<s' : q < s'
           q<s' = trans-< {_} {_} {_} {q} {r} {s'} q<r (trans-< {_} {_} {_} {r} {s} {s'} r<s s<s')

           rs : Iℚ
           rs = Iℚ-cons r s (inj-l r<s)

           qs' : Iℚ
           qs' = Iℚ-cons q s' (inj-l q<s')

           rs⊂qs' : rs i⊂ qs'
           rs⊂qs' = i⊂-cons q<r s<s'

           handle2 : Σ[ kl ∈ ℚ ] (Pos kl × kl < 1r × i-scale kl rs i⊆ qs') ->
                     Σ[ ku ∈ ℚ ] (Pos ku × 1r < ku × i-scale ku rs i⊆ qs') ->
                     1x.L q
           handle2 (kl , p-kl , kl<1 , scale-kl) (ku , p-ku , 1<ku , scale-ku) =
             ∣ k , rs , (kl<1 , 1<ku) , (xl-r , xu-s) , _i⊆_.l prod-⊆ ∣
             where
             kl<ku = trans-< {_} {_} {_} {kl} {1r} {ku} kl<1 1<ku
             k : Iℚ
             k = (Iℚ-cons kl ku (inj-l kl<ku))

             prod-⊆ : (k i* rs) i⊆ qs'
             prod-⊆ = subst ((k i* rs) i⊆_) (i∪-same qs') (i∪-preserves-⊆ scale-kl scale-ku)

      i .fun 1xl-q = unsquash (x.isProp-L q) (∥-map handle 1xl-q)
        where
        handle : L' 1ℝ x q -> x.L q
        handle ((Iℚ-cons 1i-l 1i-u 1i-l≤u) , xi@(Iℚ-cons xi-l xi-u xi-l≤u) ,
                 (1i-l<1 , 1<1i-u) , exi , q≤prod) =
          isLowerSet≤ q xi-l ans (fst exi)
          where


          l-1 : (Iℚ.l (i-scale 1i-l xi)) == (minℚ (1i-l r* xi-l) (1i-l r* xi-u))
          l-1 = refl


          u-1 : (Iℚ.l (i-scale 1i-u xi)) == (minℚ (1i-u r* xi-l) (1i-u r* xi-u))
          u-1 = refl


          check : q ℚ≤ (minℚ (Iℚ.l (i-scale 1i-l xi)) (Iℚ.l (i-scale 1i-u xi)))
          check = q≤prod

          ans : q ℚ≤ xi-l
          ans = handle2 (split-< xi-l 0r)
            where
            handle2 : (xi-l < 0r) ⊎ (0r ℚ≤ xi-l) -> q ℚ≤ xi-l
            handle2 (inj-l xi-l<0) =
              trans-ℚ≤ {q} {p0} {xi-l} q≤prod
                (trans-ℚ≤ {p0} {p2} {xi-l} lt3
                  (trans-ℚ≤ {p2} {p3} {xi-l} lt2 (inj-l lt1)))
              where
              n-xi-l : Neg xi-l
              n-xi-l = <0-Neg xi-l xi-l<0

              p1 = (Iℚ.l (i-scale 1i-l xi))
              p2 = (Iℚ.l (i-scale 1i-u xi))
              p0 = minℚ p1 p2
              p3 = (1i-u r* xi-l)
              p4 = (1i-u r* xi-u)


              lt1 : (1i-u r* xi-l) < xi-l
              lt1 = subst ((1i-u r* xi-l) <_) (r*-left-one xi-l)
                          (r*₂-flips-order 1r 1i-u (xi-l , n-xi-l) 1<1i-u)
              lt2 : (minℚ p3 p4) ℚ≤ p3
              lt2 = minℚ-≤-left p3 p4
              lt3 : (minℚ p1 p2) ℚ≤ p2
              lt3 = minℚ-≤-right p1 p2
            handle2 (inj-r 0≤xi-l) =
              trans-ℚ≤ {q} {p0} {xi-l} q≤prod
                (trans-ℚ≤ {p0} {p1} {xi-l} lt3
                  (trans-ℚ≤ {p1} {p3} {xi-l} lt2 lt1))
              where
              nn-xi-l : NonNeg xi-l
              nn-xi-l = 0≤-NonNeg xi-l 0≤xi-l


              p1 = (Iℚ.l (i-scale 1i-l xi))
              p2 = (Iℚ.l (i-scale 1i-u xi))
              p0 = minℚ p1 p2
              p3 = (1i-l r* xi-l)
              p4 = (1i-l r* xi-u)

              lt1 : (1i-l r* xi-l) ℚ≤ xi-l
              lt1 = subst ((1i-l r* xi-l) ℚ≤_) (r*-left-one xi-l)
                          (r*₂-preserves-≤ 1i-l 1r (xi-l , nn-xi-l) (inj-l 1i-l<1))
              lt2 : (minℚ p3 p4) ℚ≤ p3
              lt2 = minℚ-≤-left p3 p4
              lt3 : (minℚ p1 p2) ℚ≤ p1
              lt3 = minℚ-≤-left p1 p2


    U-path : (q : ℚ) -> 1x.U q == x.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (1x.U q) (x.U q)
      i .rightInv _ = x.isProp-U q _ _
      i .leftInv _ = 1x.isProp-U q _ _
      i .inv xu-q = ∥-bind2 handle x.Inhabited-L (x.isLowerOpen-U q xu-q)
         where
         handle : Σ ℚ x.L -> Σ[ r ∈ ℚ ] (r < q × x.U r) -> 1x.U q
         handle (s , xl-s) (r , r<q , xu-r) =
           handle2 (find-shrink-factor sr⊂s'q) (find-growth-factor sr⊂s'q)
           where

           s' : ℚ
           s' = s r+ (r- 1r)

           s'<s : s' < s
           s'<s = subst Pos (sym (diffℚ-step s 1r) >=> cong (s r+_) (diffℚ-anticommute s 1r))
                        Pos-1r

           s<r : s < r
           s<r = (ℝ-bounds->ℚ< x _ _ xl-s xu-r)

           s'<q : s' < q
           s'<q = trans-< {_} {_} {_} {s'} {r} {q} (trans-< {_} {_} {_} {s'} {s} {r} s'<s s<r) r<q

           sr : Iℚ
           sr = Iℚ-cons s r (inj-l s<r)

           s'q : Iℚ
           s'q = Iℚ-cons s' q (inj-l s'<q)

           sr⊂s'q : sr i⊂ s'q
           sr⊂s'q = i⊂-cons s'<s r<q

           handle2 : Σ[ kl ∈ ℚ ] (Pos kl × kl < 1r × i-scale kl sr i⊆ s'q) ->
                     Σ[ ku ∈ ℚ ] (Pos ku × 1r < ku × i-scale ku sr i⊆ s'q) ->
                     1x.U q
           handle2 (kl , p-kl , kl<1 , scale-kl) (ku , p-ku , 1<ku , scale-ku) =
             ∣ k , sr , (kl<1 , 1<ku) , (xl-s , xu-r) , _i⊆_.u prod-⊆ ∣
             where
             kl<ku = trans-< {_} {_} {_} {kl} {1r} {ku} kl<1 1<ku
             k : Iℚ
             k = (Iℚ-cons kl ku (inj-l kl<ku))

             prod-⊆ : (k i* sr) i⊆ s'q
             prod-⊆ = subst ((k i* sr) i⊆_) (i∪-same s'q) (i∪-preserves-⊆ scale-kl scale-ku)

      i .fun 1xu-q = unsquash (x.isProp-U q) (∥-map handle 1xu-q)
        where
        handle : U' 1ℝ x q -> x.U q
        handle ((Iℚ-cons 1i-l 1i-u 1i-l≤u) , xi@(Iℚ-cons xi-l xi-u xi-l≤u) ,
                 (1i-l<1 , 1<1i-u) , exi , prod≤q) =
          isUpperSet≤ xi-u q ans (snd exi)
          where

          ans : xi-u ℚ≤ q
          ans = (handle2 (split-< xi-u 0r))
            where
            handle2 : (xi-u < 0r) ⊎ (0r ℚ≤ xi-u) -> xi-u ℚ≤ q
            handle2 (inj-l xi-u<0) =
              trans-ℚ≤ {xi-u} {p0} {q}
                (trans-ℚ≤ {xi-u} {p1} {p0}
                  (trans-ℚ≤ {xi-u} {p4} {p1} (inj-l lt1) lt2)
                  lt3)
                prod≤q
              where
              n-xi-u : Neg xi-u
              n-xi-u = <0-Neg xi-u xi-u<0

              p1 = (Iℚ.u (i-scale 1i-l xi))
              p2 = (Iℚ.u (i-scale 1i-u xi))
              p0 = maxℚ p1 p2
              p3 = (1i-l r* xi-l)
              p4 = (1i-l r* xi-u)


              lt1 : xi-u < (1i-l r* xi-u)
              lt1 = subst (_< (1i-l r* xi-u)) (r*-left-one xi-u)
                          (r*₂-flips-order 1i-l 1r (xi-u , n-xi-u) 1i-l<1)

              lt2 : p4 ℚ≤ (maxℚ p3 p4)
              lt2 = maxℚ-≤-right p3 p4
              lt3 : p1 ℚ≤ (maxℚ p1 p2)
              lt3 = maxℚ-≤-left p1 p2

            handle2 (inj-r 0≤xi-u) =
              trans-ℚ≤ {xi-u} {p0} {q}
                (trans-ℚ≤ {xi-u} {p2} {p0}
                  (trans-ℚ≤ {xi-u} {p4} {p2} lt1 lt2)
                  lt3)
                prod≤q
              where
              nn-xi-u : NonNeg xi-u
              nn-xi-u = 0≤-NonNeg xi-u 0≤xi-u


              p1 = (Iℚ.u (i-scale 1i-l xi))
              p2 = (Iℚ.u (i-scale 1i-u xi))
              p0 = maxℚ p1 p2
              p3 = (1i-u r* xi-l)
              p4 = (1i-u r* xi-u)

              lt1 : xi-u ℚ≤ (1i-u r* xi-u)
              lt1 = subst (_ℚ≤ (1i-u r* xi-u)) (r*-left-one xi-u)
                          (r*₂-preserves-≤ 1r 1i-u (xi-u , nn-xi-u) (inj-l 1<1i-u))
              lt2 : p4 ℚ≤ (maxℚ p3 p4)
              lt2 = maxℚ-≤-right p3 p4
              lt3 : p2 ℚ≤ (maxℚ p1 p2)
              lt3 = maxℚ-≤-right p1 p2


  ℝ*-left-one : 1x == x
  ℝ*-left-one = LU-paths->path 1x x L-path U-path


module _ (x : ℝ)
  where
  private
    module x = Real x
    module 0ℝ = Real 0ℝ
    0x = 0ℝ ℝ* x
    module 0x = Real 0x


    L-path : (q : ℚ) -> 0x.L q == 0ℝ.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (0x.L q) (0ℝ.L q)
      i .rightInv _ = 0ℝ.isProp-L q _ _
      i .leftInv _ = 0x.isProp-L q _ _
      i .inv 0ℝl-q = unsquash (0x.isProp-L q) (∥-map2 handle x.Inhabited-L x.Inhabited-U)
        where
        handle : Σ ℚ x.L -> Σ ℚ x.U -> 0x.L q
        handle (p1 , xl-p1) (p2 , xu-p2) =
          ∣ ir , ix , (Neg-<0 r neg-r , Pos-0< mr pos-mr) , (xl-p1 , xu-p2) , ans ∣
          where
          ix : Iℚ
          ix = Iℚ-cons p1 p2 (inj-l (ℝ-bounds->ℚ< x _ _ xl-p1 xu-p2))

          m = i-maxabs ix

          pos-m : Pos m
          pos-m = handle2 (NonNeg-i-maxabs ix)
            where
            handle2 : NonNeg m -> Pos m
            handle2 (inj-l p) = p
            handle2 (inj-r z) = bot-elim (x.disjoint 0r (subst x.L (cong Iℚ.l zp) xl-p1 ,
                                                         subst x.U (cong Iℚ.u zp) xu-p2))
              where
              zp = i-maxabs-Zero ix z

          inv-m = Pos->Inv pos-m
          1/m = (r1/ m inv-m)
          pos-1/m = r1/-preserves-Pos m inv-m pos-m

          r = q r* 1/m

          neg-q = <0-Neg q 0ℝl-q

          neg-r = r*₁-flips-sign (q , neg-q) 1/m pos-1/m

          mr = r- r


          pos-mr = r--flips-sign r _ neg-r
          r≤mr = NonPos≤NonNeg (inj-l neg-r) (inj-l pos-mr)

          ir = Iℚ-cons r mr r≤mr

          m-ir = i-maxabs ir

          lb = Iℚ.l (ir i* ix)
          ub = Iℚ.u (ir i* ix)
          m2 = i-maxabs (ir i* ix)

          -lb≤m2 : (r- lb) ℚ≤ m2
          -lb≤m2 = trans-ℚ≤ {r- lb} {absℚ lb} {m2} (maxℚ-≤-right lb (r- lb))
                                                   (maxℚ-≤-left (absℚ lb) (absℚ ub))
          -m2≤lb : (r- m2) ℚ≤ lb
          -m2≤lb = subst ((r- m2) ℚ≤_) (RationalRing.minus-double-inverse {lb})
                         (r--flips-≤ (r- lb) m2 -lb≤m2)

          m2=m-ir*m : m2 == m-ir r* m
          m2=m-ir*m = i-maxabs-i* ir ix

          m-ir=r : m-ir == (r- r)
          m-ir=r = cong (maxℚ (absℚ r)) (cong (maxℚ (r- r)) (RationalRing.minus-double-inverse {r}) >=>
                                         maxℚ-commute) >=>
                   maxℚ-same >=>
                   absℚ-NonPos (inj-l neg-r)

          mr*m=-q : (r- r) r* m == (r- q)
          mr*m=-q = cong (_r* m) (sym (r*-minus-extract-left q 1/m)) >=>
                    r*-assoc (r- q) 1/m m >=>
                    cong ((r- q) r*_) (r1/-inverse m inv-m) >=>
                    r*-right-one (r- q)

          -lb≤-q : (r- lb) ℚ≤ (r- q)
          -lb≤-q = subst ((r- lb) ℚ≤_)
                         (m2=m-ir*m >=> (cong (_r* m) m-ir=r) >=> mr*m=-q)
                         -lb≤m2

          ans : q ℚ≤ lb
          ans = subst2 _ℚ≤_ (RationalRing.minus-double-inverse {q})
                            (RationalRing.minus-double-inverse {lb})
                            (r--flips-≤ (r- lb) (r- q) -lb≤-q)


      i .fun 0x-q = unsquash (0ℝ.isProp-L q) (∥-map handle 0x-q)
        where
        handle : L' 0ℝ x q -> 0ℝ.L q
        handle (0i@(Iℚ-cons 0i-l 0i-u 0i-l≤u) , xi@(Iℚ-cons xi-l xi-u xi-l≤u) ,
                (0i-ll , 0i-uu) , exi , q≤prod) =
          Neg-<0 q (Neg-≤ q p0 n-p0 q≤prod)
          where
          n-l : Neg 0i-l
          n-l = <0-Neg 0i-l 0i-ll
          p-u : Pos 0i-u
          p-u = 0<-Pos 0i-u 0i-uu

          p1 = (Iℚ.l (i-scale 0i-l xi))
          p2 = (Iℚ.l (i-scale 0i-u xi))
          p0 = minℚ p1 p2

          n-p0 : Neg p0
          n-p0 = fst (i*₁-StrictCrossZero 0i xi (n-l , p-u) (ℝ∈Iℚ->NonConstant x xi exi))


    U-path : (q : ℚ) -> 0x.U q == 0ℝ.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (0x.U q) (0ℝ.U q)
      i .rightInv _ = 0ℝ.isProp-U q _ _
      i .leftInv _ = 0x.isProp-U q _ _
      i .inv 0ℝu-q = unsquash (0x.isProp-U q) (∥-map2 handle x.Inhabited-L x.Inhabited-U)
        where
        handle : Σ ℚ x.L -> Σ ℚ x.U -> 0x.U q
        handle (p1 , xl-p1) (p2 , xu-p2) =
          ∣ ir , ix , (Neg-<0 mr neg-mr , Pos-0< r pos-r) , (xl-p1 , xu-p2) , ub≤q ∣
          where
          ix : Iℚ
          ix = Iℚ-cons p1 p2 (inj-l (ℝ-bounds->ℚ< x _ _ xl-p1 xu-p2))

          m = i-maxabs ix

          pos-m : Pos m
          pos-m = handle2 (NonNeg-i-maxabs ix)
            where
            handle2 : NonNeg m -> Pos m
            handle2 (inj-l p) = p
            handle2 (inj-r z) = bot-elim (x.disjoint 0r (subst x.L (cong Iℚ.l zp) xl-p1 ,
                                                         subst x.U (cong Iℚ.u zp) xu-p2))
              where
              zp = i-maxabs-Zero ix z

          inv-m = Pos->Inv pos-m
          1/m = (r1/ m inv-m)
          pos-1/m = r1/-preserves-Pos m inv-m pos-m

          r = q r* 1/m

          pos-q = 0<-Pos q 0ℝu-q

          pos-r = r*₁-preserves-sign (q , pos-q) 1/m pos-1/m

          mr = r- r


          neg-mr = r--flips-sign r _ pos-r
          mr≤r = NonPos≤NonNeg (inj-l neg-mr) (inj-l pos-r)

          ir = Iℚ-cons mr r mr≤r

          m-ir = i-maxabs ir

          lb = Iℚ.l (ir i* ix)
          ub = Iℚ.u (ir i* ix)
          m2 = i-maxabs (ir i* ix)

          ub≤m2 : ub ℚ≤ m2
          ub≤m2 = trans-ℚ≤ {ub} {absℚ ub} {m2} (maxℚ-≤-left ub (r- ub))
                                               (maxℚ-≤-right (absℚ lb) (absℚ ub))

          m2=m-ir*m : m2 == m-ir r* m
          m2=m-ir*m = i-maxabs-i* ir ix

          m-ir=r : m-ir == r
          m-ir=r = cong (\x -> (maxℚ x (absℚ r)))
                        (cong (maxℚ (r- r)) (RationalRing.minus-double-inverse {r}) >=>
                         maxℚ-commute) >=>
                   maxℚ-same >=>
                   absℚ-NonNeg (inj-l pos-r)

          mr*m=q : r r* m == q
          mr*m=q = r*-assoc q 1/m m >=>
                   cong (q r*_) (r1/-inverse m inv-m) >=>
                   r*-right-one q

          ub≤q : ub ℚ≤ q
          ub≤q = subst (ub ℚ≤_)
                       (m2=m-ir*m >=> (cong (_r* m) m-ir=r) >=> mr*m=q)
                       ub≤m2

      i .fun 0x-q = unsquash (0ℝ.isProp-U q) (∥-map handle 0x-q)
        where
        handle : U' 0ℝ x q -> 0ℝ.U q
        handle (0i@(Iℚ-cons 0i-l 0i-u 0i-l≤u) , xi@(Iℚ-cons xi-l xi-u xi-l≤u) ,
                (0i-ll , 0i-uu) , exi , prod≤q) =
          Pos-0< q (Pos-≤ p0 q p-p0 prod≤q)
          where
          n-l : Neg 0i-l
          n-l = <0-Neg 0i-l 0i-ll
          p-u : Pos 0i-u
          p-u = 0<-Pos 0i-u 0i-uu

          p1 = (Iℚ.u (i-scale 0i-l xi))
          p2 = (Iℚ.u (i-scale 0i-u xi))
          p0 = maxℚ p1 p2

          p-p0 : Pos p0
          p-p0 = snd (i*₁-StrictCrossZero 0i xi (n-l , p-u) (ℝ∈Iℚ->NonConstant x xi exi))

  ℝ*-left-zero : 0x == 0ℝ
  ℝ*-left-zero = LU-paths->path 0x 0ℝ L-path U-path
