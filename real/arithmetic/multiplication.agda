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
open import real
open import real.sequence
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation
open import univalence

private
  ℝ∈Iℚ : ℝ -> Iℚ -> Type₀
  ℝ∈Iℚ z (Iℚ-cons l u _) = Real.L z l × Real.U z u

  module _ (x y : ℝ) where
    L' : Pred ℚ ℓ-zero
    L' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Lower (xi i* yi) q)

    U' : Pred ℚ ℓ-zero
    U' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Upper (xi i* yi) q)

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


-- module _ (x : ℝ)
--   (i-centered : ℚ -> ℚ⁺ -> Iℚ)
--   where
--   private
--     module x = Real x
--     module 1ℝ = Real 1ℝ
--     1x = 1ℝ ℝ* x
--     module 1x = Real 1x
--
--     1∈centered : (ε : ℚ⁺) -> ℝ∈Iℚ 1ℝ (i-centered 1r ε)
--     1∈centered = ?
--
--     L-path : (q : ℚ) -> 1x.L q == x.L q
--     L-path q = ua (isoToEquiv i)
--       where
--       open Iso
--       i : Iso (1x.L q) (x.L q)
--       i .rightInv _ = x.isProp-L q _ _
--       i .leftInv _ = 1x.isProp-L q _ _
--       i .inv xl-q = ∥-bind2 handle x.Inhabited-U (x.isUpperOpen-L q xl-q)
--          where
--          handle : Σ ℚ x.U -> Σ[ r ∈ ℚ ] (q < r × x.L r) -> 1x.L q
--          handle (s , xu-s) (r , q<r , xl-r) =
--            ∣ i-centered 1r ε⁺ , rs , 1∈centered ε⁺ , (xl-r , xu-s) , ? ∣
--            where
--            ε : ℚ
--            ε = ?
--            ε⁺ : ℚ⁺
--            ε⁺ = ε , ?
--
--            rs : Iℚ
--            rs = Iℚ-cons r s (inj-l (ℝ-bounds->ℚ< x _ _ xl-r xu-s))
--
--            -- path : (diffℚ r q) r+ r == q
--            -- path = r+-commute (diffℚ r q) r >=> diffℚ-step r q
--
--            -- d'>0 : (diffℚ q r) > 0r
--            -- d'>0 = Pos-0< _ q<r
--
--            -- d<0 : (diffℚ r q) < 0r
--            -- d<0 = subst (_< 0r) (sym (diffℚ-anticommute r q)) (r--flips-order 0r (diffℚ q r) d'>0)
--
--       i .fun 0xl-q = ?

--       i .fun 0xl-q = unsquash (x.isProp-L q) (∥-map handle 0xl-q)
--         where
--         handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (1ℝ.L a × x.L b × a r+ b == q) -> x.L q
--         handle (a , b , 0l-a , xl-b , p) = x.isLowerSet-L q b q<b xl-b
--           where
--           q<b : q < b
--           q<b = subst2 _<_ p (r+-left-zero b) (r+₂-preserves-order a 0r b 0l-a)
--
--    U-path : (q : ℚ) -> 0x.U q == x.U q
--    U-path q = ua (isoToEquiv i)
--      where
--      open Iso
--      i : Iso (0x.U q) (x.U q)
--      i .rightInv _ = x.isProp-U q _ _
--      i .leftInv _ = 0x.isProp-U q _ _
--      i .inv xu-q = ∥-bind handle (x.isLowerOpen-U q xu-q)
--        where
--        handle : Σ[ r ∈ ℚ ] (r < q × x.U r) -> 0x.U q
--        handle (r , r<q , xu-r) = ∣ (diffℚ r q) , r , 0<d , xu-r , path ∣
--          where
--          path : (diffℚ r q) r+ r == q
--          path = r+-commute (diffℚ r q) r >=> diffℚ-step r q
--
--          0<d : 0r < (diffℚ r q)
--          0<d = Pos-0< _ r<q
--      i .fun 0xu-q = unsquash (x.isProp-U q) (∥-map handle 0xu-q)
--        where
--        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (0ℝ.U a × x.U b × a r+ b == q) -> x.U q
--        handle (a , b , 0u-a , xu-b , p) = x.isUpperSet-U b q b<q xu-b
--          where
--          b<q : b < q
--          b<q = subst2 _<_ (r+-left-zero b) p (r+₂-preserves-order 0r a b 0u-a)
--
--
--  ℝ+-left-zero : 0x == x
--  ℝ+-left-zero = LU-paths->path 0x x L-path U-path
