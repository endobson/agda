{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication where

open import additive-group
open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.non-trivial
open import ordered-semiring.non-trivial.instances.rational
open import rational
open import rational.order
open import rational.open-interval
open import rational.open-interval.maxabs-multiplication
open import rational.open-interval.multiplication-inclusion
open import rational.open-interval.multiplication-strict-cross-zero
open import real
open import real.open-interval
open import real.order
open import real.rational
open import real.sequence
open import relation hiding (U)
open import ring.implementations.rational
open import semiring
open import sign
open import sign.instances.rational
open import truncation
open import univalence

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
      handle (r , q<r , lr) = handle2 (decide-sign r)
        where
        handle2 : Σ[ s ∈ Sign ] (isSign s r) -> Ans
        handle2 (pos-sign , pr) = ∣ r , inj-l pr , q<r , lr ∣
        handle2 (neg-sign , nr) = ∣ r , inj-r nr , q<r , lr ∣
        handle2 (zero-sign , zr) = ∥-bind handle3 (Real.isUpperOpen-L z r lr)
          where
          handle3 : Σ[ r2 ∈ ℚ ] (r < r2 × Real.L z r2) -> Ans
          handle3 (r2 , r<r2 , lr2) = ∣ r2 , inj-l pr2 , trans-< q<r r<r2 , lr2 ∣
            where
            pr2 : 0# < r2
            pr2 = trans-=-< (sym zr) r<r2

    NonZero-LowerOpen : (z : ℝ) (q : ℚ) (l : Real.U z q) -> ∃[ r ∈ ℚ ] (NonZero r × r < q × Real.U z r)
    NonZero-LowerOpen z q uq = ∥-bind handle (Real.isLowerOpen-U z q uq)
      where
      Ans = ∃[ r ∈ ℚ ] (NonZero r × r < q × Real.U z r)
      handle : Σ[ r ∈ ℚ ] (r < q × Real.U z r) -> Ans
      handle (r , r<q , ur) = handle2 (decide-sign r)
        where
        handle2 : Σ[ s ∈ Sign ] (isSign s r) -> Ans
        handle2 (pos-sign , pr) = ∣ r , inj-l pr , r<q , ur ∣
        handle2 (neg-sign , nr) = ∣ r , inj-r nr , r<q , ur ∣
        handle2 (zero-sign , zr) = ∥-bind handle3 (Real.isLowerOpen-U z r ur)
          where
          handle3 : Σ[ r2 ∈ ℚ ] (r2 < r × Real.U z r2) -> Ans
          handle3 (r2 , r2<r , ur2) = ∣ r2 , inj-r nr2 , trans-< r2<r r<q , ur2 ∣
            where
            nr2 : r2 < 0#
            nr2 = trans-<-= r2<r zr

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-map4 handle x.Inhabited-L x.Inhabited-U y.Inhabited-L y.Inhabited-U
      where
      handle : Σ ℚ x.L -> Σ ℚ x.U -> Σ ℚ y.L -> Σ ℚ y.U -> Σ ℚ L
      handle (a , la) (b , ub) (c , lc) (d , ud) =
        q , ∣ ab , cd , (la , ub) , (lc , ud) , refl-ℚ≤ {q} ∣
        where
        ab : Iℚ
        ab = ℝ-bounds->Iℚ x la ub
        cd : Iℚ
        cd = ℝ-bounds->Iℚ y lc ud
        q = Iℚ.l (ab i* cd)

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map4 handle x.Inhabited-L x.Inhabited-U y.Inhabited-L y.Inhabited-U
      where
      handle : Σ ℚ x.L -> Σ ℚ x.U -> Σ ℚ y.L -> Σ ℚ y.U -> Σ ℚ U
      handle (a , la) (b , ub) (c , lc) (d , ud) =
        q , ∣ ab , cd , (la , ub) , (lc , ud) , refl-ℚ≤ {q} ∣
        where
        ab : Iℚ
        ab = ℝ-bounds->Iℚ x la ub
        cd : Iℚ
        cd = ℝ-bounds->Iℚ y lc ud
        q = Iℚ.u (ab i* cd)

    isLowerSet-L : isLowerSet L
    isLowerSet-L {a} {b} a<b = ∥-map handle
      where
      handle : L' x y b -> L' x y a
      handle (xi , yi , exi , eyi , lt) =
        (xi , yi , exi , eyi , weaken-< (trans-<-≤ a<b lt))

    isUpperSet-U : isUpperSet U
    isUpperSet-U {a} {b} a<b = ∥-map handle
      where
      handle : U' x y a -> U' x y b
      handle (xi , yi , exi , eyi , lt) =
        (xi , yi , exi , eyi , weaken-< (trans-≤-< lt a<b))

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' x y q -> ∃[ r ∈ ℚ ] (q < r × L r)
      handle (xi , yi , x∈xi , y∈yi , lt) =
        ∥-map2 handle2 (tighter-ℝ∈Iℚ x xi x∈xi) (tighter-ℝ∈Iℚ y yi y∈yi)
        where
        handle2 : Σ[ xi' ∈ Iℚ ] (xi' i⊂ xi × ℝ∈Iℚ x xi') ->
                  Σ[ yi' ∈ Iℚ ] (yi' i⊂ yi × ℝ∈Iℚ y yi') ->
                  Σ[ r ∈ ℚ ] (q < r × L r)
        handle2 (xi' , xi'⊂xi , x∈xi') (yi' , yi'⊂yi , y∈yi') =
          r , q<r , ∣ xi' , yi' , x∈xi' , y∈yi' , refl-≤ ∣
          where
          r = Iℚ.l (xi' i* yi')

          p'⊂p : (xi' i* yi') i⊂ (xi i* yi)
          p'⊂p = i*-preserves-⊂ xi'⊂xi yi'⊂yi

          q<r : q < r
          q<r = trans-≤-< lt (_i⊂_.l p'⊂p)


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-bind handle
      where
      handle : U' x y q -> ∃[ r ∈ ℚ ] (r < q × U r)
      handle (xi , yi , x∈xi , y∈yi , lt) =
        ∥-map2 handle2 (tighter-ℝ∈Iℚ x xi x∈xi) (tighter-ℝ∈Iℚ y yi y∈yi)
        where
        handle2 : Σ[ xi' ∈ Iℚ ] (xi' i⊂ xi × ℝ∈Iℚ x xi') ->
                  Σ[ yi' ∈ Iℚ ] (yi' i⊂ yi × ℝ∈Iℚ y yi') ->
                  Σ[ r ∈ ℚ ] (r < q × U r)
        handle2 (xi' , xi'⊂xi , x∈xi') (yi' , yi'⊂yi , y∈yi') =
          r , r<q , ∣ xi' , yi' , x∈xi' , y∈yi' , refl-≤ ∣
          where
          r = Iℚ.u (xi' i* yi')

          p'⊂p : (xi' i* yi') i⊂ (xi i* yi)
          p'⊂p = i*-preserves-⊂ xi'⊂xi yi'⊂yi

          r<q : r < q
          r<q = trans-<-≤ (_i⊂_.u p'⊂p) lt



    disjoint : Universal (Comp (L ∩ U))
    disjoint q (lq , uq) = unsquash isPropBot (∥-map2 handle lq uq)
      where
      handle : L' x y q -> U' x y q -> Bot
      handle (xi1 , yi1 , exi1 , eyi1 , l1) (xi2 , yi2 , exi2 , eyi2 , u2) =
        ¬LowerUpper p3 l3 u3
        where
        xi3 : Iℚ
        xi3 = i-intersect xi1 xi2 (ℝ∈Iℚ->Overlap x xi1 xi2 exi1 exi2)

        yi3 : Iℚ
        yi3 = i-intersect yi1 yi2 (ℝ∈Iℚ->Overlap y yi1 yi2 eyi1 eyi2)

        xi3⊆xi1 : xi3 i⊆ xi1
        xi3⊆xi1 = i-intersect-⊆₁ xi1 xi2 (ℝ∈Iℚ->Overlap x xi1 xi2 exi1 exi2)
        xi3⊆xi2 : xi3 i⊆ xi2
        xi3⊆xi2 = i-intersect-⊆₂ xi1 xi2 (ℝ∈Iℚ->Overlap x xi1 xi2 exi1 exi2)
        yi3⊆yi1 : yi3 i⊆ yi1
        yi3⊆yi1 = i-intersect-⊆₁ yi1 yi2 (ℝ∈Iℚ->Overlap y yi1 yi2 eyi1 eyi2)
        yi3⊆yi2 : yi3 i⊆ yi2
        yi3⊆yi2 = i-intersect-⊆₂ yi1 yi2 (ℝ∈Iℚ->Overlap y yi1 yi2 eyi1 eyi2)

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

    located : (a b : ℚ) -> a < b -> ∥ L a ⊎ U b ∥
    located a b a<b = ∥-bind4 initial-bound x.Inhabited-L x.Inhabited-U y.Inhabited-L y.Inhabited-U
      where
      Ans = ∥ L a ⊎ U b ∥
      d = diff a b
      0<d = diff-0<⁺ a<b

      initial-bound : Σ ℚ x.L -> Σ ℚ x.U -> Σ ℚ y.L -> Σ ℚ y.U -> Ans
      initial-bound (xb1' , xbl') (xb2' , xbu') (yb1' , ybl') (yb2' , ybu') =
        ∥-bind2 handle (find-open-ball x ε⁺) (find-open-ball y ε⁺)
        where

        xi' : Iℚ
        xi' = ℝ-bounds->Iℚ x xbl' xbu'
        yi' : Iℚ
        yi' = ℝ-bounds->Iℚ y ybl' ybu'

        m-xi' = i-maxabs xi'
        m-yi' = i-maxabs yi'

        exi' : ℝ∈Iℚ x xi'
        exi' = xbl' , xbu'

        eyi' : ℝ∈Iℚ y yi'
        eyi' = ybl' , ybu'

        0<m-xi' : 0# < m-xi'
        0<m-xi' = 0<i-maxabs xi'

        0<m-yi' : 0# < m-yi'
        0<m-yi' = 0<i-maxabs yi'


        sm = (m-yi' r+ m-xi')
        0<sm = +-preserves-0< 0<m-yi' 0<m-xi'

        sm-inv : ℚInv sm
        sm-inv z-sm = irrefl-< (trans-<-= 0<sm z-sm)

        ε = (d r* (r1/ sm sm-inv))

        ε⁺ : ℚ⁺
        ε⁺ = ε , (r*₁-preserves-sign (d , 0<d) _ {pos-sign}
                                     (r1/-preserves-Pos sm sm-inv 0<sm))

        ε-path : (ε r* (m-yi' r+ m-xi')) == d
        ε-path = r*-assoc _ _ _ >=>
                 (cong (d r*_) (r1/-inverse sm sm-inv)) >=>
                 (r*-right-one d)



        handle : OpenBall x ε  -> OpenBall y ε -> Ans
        handle (xb1 , xb2 , xbl , xbu , xbe) (yb1 , yb2 , ybl , ybu , ybe) =
          handle2 (split-< a l)
          where
          xi : Iℚ
          xi = ℝ-bounds->Iℚ x xbl xbu
          yi : Iℚ
          yi = ℝ-bounds->Iℚ y ybl ybu

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

          0≤w-mxi = weaken-< (0<i-width mxi)
          0≤w-myi = weaken-< (0<i-width myi)

          0≤m-xi' = weaken-< (0<i-maxabs xi')
          0≤m-yi' = weaken-< (0<i-maxabs yi')

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
                             (*₁-preserves-≤ 0≤w-mxi m-myi≤m-yi')
                             (*₂-preserves-≤ w-mxi≤ε 0≤m-yi')

          mw-xy-≤ : (m-mxi r* w-myi) ℚ≤ (ε r* m-xi')
          mw-xy-≤ = trans-ℚ≤ {(m-mxi r* w-myi)} {(m-xi' r* w-myi)} {(ε r* m-xi')}
                             (*₂-preserves-≤ m-mxi≤m-xi' 0≤w-myi)
                             (subst ((m-xi' r* w-myi) ℚ≤_) (r*-commute m-xi' ε)
                                    (*₁-preserves-≤ 0≤m-xi' w-myi≤ε))

          wmmw = ((w-mxi r* m-myi) r+ (m-mxi r* w-myi))
          wmmw≤d : wmmw ℚ≤ d
          wmmw≤d =
            subst (wmmw ℚ≤_) (sym *-distrib-+-left >=> ε-path)
                  (+-preserves-≤ wm-xy-≤ mw-xy-≤)


          p = mxi i* myi
          l = Iℚ.l p
          u = Iℚ.u p
          w = i-width p

          w≤wmmw : w ℚ≤ wmmw
          w≤wmmw = i*-width-≤ mxi myi

          w≤d : w ℚ≤ d
          w≤d = trans-ℚ≤ {w} {wmmw} {d} w≤wmmw wmmw≤d

          handle2 : (a < l ⊎ l ℚ≤ a) -> Ans
          handle2 (inj-l a<l) = ∣ inj-l ∣ (mxi , myi , emxi , emyi , (weaken-< a<l)) ∣ ∣
          handle2 (inj-r l≤a) = ∣ inj-r ∣ (mxi , myi , emxi , emyi , u≤b) ∣ ∣
            where
            u≤b : u ℚ≤ b
            u≤b = subst2 _ℚ≤_ diff-step diff-step (+-preserves-≤ l≤a w≤d)

  _ℝ*ᵉ_ : ℝ
  _ℝ*ᵉ_ = record
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

abstract
  _ℝ*_ : ℝ -> ℝ -> ℝ
  a ℝ* b = a ℝ*ᵉ b

  ℝ*-eval : {a b : ℝ} -> a ℝ* b == a ℝ*ᵉ b
  ℝ*-eval = refl

module _ (x y : ℝ) where
  private
    module x = Real x
    module y = Real y
    xy = x ℝ*ᵉ y
    yx = y ℝ*ᵉ x
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

    ℝ*ᵉ-commute : xy == yx
    ℝ*ᵉ-commute = LU-paths->path xy yx L-path U-path

  abstract
    ℝ*-commute : x ℝ* y == y ℝ* x
    ℝ*-commute = ℝ*ᵉ-commute



module _ (x : ℝ)
  where
  private
    module x = Real x
    module 1ℝ = Real 1ℝ
    1x = 1ℝ ℝ*ᵉ x
    module 1x = Real 1x

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
           s' = 1r + s

           s<s' : s < s'
           s<s' = trans-=-< (sym +-left-zero) (+₂-preserves-< 0<1)

           r<s : r < s
           r<s = ℝ-bounds->ℚ< x xl-r xu-s

           q<s' : q < s'
           q<s' = trans-< q<r (trans-< r<s s<s')

           rs : Iℚ
           rs = Iℚ-cons r s r<s

           qs' : Iℚ
           qs' = Iℚ-cons q s' q<s'

           rs⊂qs' : rs i⊂ qs'
           rs⊂qs' = i⊂-cons q<r s<s'

           handle2 : Σ[ kl⁺@(kl , _) ∈ ℚ⁺ ] (kl < 1r × i-scale⁺ kl⁺ rs i⊆ qs') ->
                     Σ[ ku⁺@(ku , _) ∈ ℚ⁺ ] (1r < ku × i-scale⁺ ku⁺ rs i⊆ qs') ->
                     1x.L q
           handle2 (kl⁺@(kl , p-kl) , kl<1 , scale-kl) (ku⁺@(ku , p-ku) , 1<ku , scale-ku) =
             ∣ k , rs , (ℚ<->L kl<1 , ℚ<->U 1<ku) , (xl-r , xu-s) , _i⊆_.l prod-⊆ ∣
             where
             kl<ku = trans-< kl<1 1<ku
             k : Iℚ
             k = Iℚ-cons kl ku kl<ku

             *-path : (i-scale⁺ kl⁺ rs i∪ i-scale⁺ ku⁺ rs) == (k i* rs)
             *-path = cong2 _i∪_ (i-scale⁺-path kl⁺ rs) (i-scale⁺-path ku⁺ rs) >=>
                      Iℚ-bounds-path refl refl

             prod-⊆ : (k i* rs) i⊆ qs'
             prod-⊆ = subst2 (_i⊆_) *-path (i∪-same qs') (i∪-preserves-⊆ scale-kl scale-ku)

      i .fun 1xl-q = unsquash (x.isProp-L q) (∥-map handle 1xl-q)
        where
        handle : L' 1ℝ x q -> x.L q
        handle ((Iℚ-cons 1i-l 1i-u 1i-l≤u) , xi@(Iℚ-cons xi-l xi-u xi-l≤u) ,
                 (1i-l<1 , 1<1i-u) , exi , q≤prod) =
          isLowerSet≤ x ans (fst exi)
          where

          ans : q ℚ≤ xi-l
          ans = handle2 (split-< xi-l 0r)
            where
            p1 = min (1i-l * xi-l) (1i-l * xi-u)
            p2 = min (1i-u * xi-l) (1i-u * xi-u)
            p0 = min p1 p2

            handle2 : (xi-l < 0r) ⊎ (0r ℚ≤ xi-l) -> q ℚ≤ xi-l
            handle2 (inj-l xi-l<0) =
              trans-ℚ≤ {q} {p0} {xi-l} q≤prod
                (trans-ℚ≤ {p0} {p2} {xi-l} lt3
                  (trans-ℚ≤ {p2} {p3} {xi-l} lt2 (weaken-< lt1)))
              where
              p3 = (1i-u r* xi-l)
              p4 = (1i-u r* xi-u)

              lt1 : (1i-u r* xi-l) < xi-l
              lt1 = subst ((1i-u r* xi-l) <_) (r*-left-one xi-l)
                          (*₂-flips-< (U->ℚ< 1<1i-u) xi-l<0)
              lt2 : (min p3 p4) ℚ≤ p3
              lt2 = min-≤-left
              lt3 : (min p1 p2) ℚ≤ p2
              lt3 = min-≤-right
            handle2 (inj-r 0≤xi-l) =
              trans-ℚ≤ {q} {p0} {xi-l} q≤prod
                (trans-ℚ≤ {p0} {p1} {xi-l} lt3
                  (trans-ℚ≤ {p1} {p3} {xi-l} lt2 lt1))
              where
              p3 = (1i-l r* xi-l)
              p4 = (1i-l r* xi-u)

              lt1 : (1i-l r* xi-l) ℚ≤ xi-l
              lt1 = subst ((1i-l r* xi-l) ℚ≤_) (r*-left-one xi-l)
                          (*₂-preserves-≤ (weaken-< (L->ℚ< 1i-l<1)) 0≤xi-l)
              lt2 : (min p3 p4) ℚ≤ p3
              lt2 = min-≤-left
              lt3 : (min p1 p2) ℚ≤ p1
              lt3 = min-≤-left


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
           s'<s = trans-<-= (+₁-preserves-< (minus-flips-0< 0<1)) +-right-zero

           s<r : s < r
           s<r = ℝ-bounds->ℚ< x xl-s xu-r

           s'<q : s' < q
           s'<q = trans-< (trans-< s'<s s<r) r<q

           sr : Iℚ
           sr = Iℚ-cons s r s<r

           s'q : Iℚ
           s'q = Iℚ-cons s' q s'<q

           sr⊂s'q : sr i⊂ s'q
           sr⊂s'q = i⊂-cons s'<s r<q

           handle2 : Σ[ kl⁺@(kl , _) ∈ ℚ⁺ ] (kl < 1r × i-scale⁺ kl⁺ sr i⊆ s'q) ->
                     Σ[ ku⁺@(ku , _) ∈ ℚ⁺ ] (1r < ku × i-scale⁺ ku⁺ sr i⊆ s'q) ->
                     1x.U q
           handle2 (kl⁺@(kl , p-kl) , kl<1 , scale-kl) (ku⁺@(ku , p-ku) , 1<ku , scale-ku) =
             ∣ k , sr , (ℚ<->L kl<1 , ℚ<->U 1<ku) , (xl-s , xu-r) , _i⊆_.u prod-⊆ ∣
             where
             kl<ku = trans-< kl<1 1<ku
             k : Iℚ
             k = Iℚ-cons kl ku kl<ku

             *-path : (i-scale⁺ kl⁺ sr i∪ i-scale⁺ ku⁺ sr) == (k i* sr)
             *-path = cong2 _i∪_ (i-scale⁺-path kl⁺ sr) (i-scale⁺-path ku⁺ sr) >=>
                      Iℚ-bounds-path refl refl

             prod-⊆ : (k i* sr) i⊆ s'q
             prod-⊆ = subst2 (_i⊆_) *-path (i∪-same s'q) (i∪-preserves-⊆ scale-kl scale-ku)

      i .fun 1xu-q = unsquash (x.isProp-U q) (∥-map handle 1xu-q)
        where
        handle : U' 1ℝ x q -> x.U q
        handle ((Iℚ-cons 1i-l 1i-u 1i-l≤u) , xi@(Iℚ-cons xi-l xi-u xi-l≤u) ,
                 (1i-l<1 , 1<1i-u) , exi , prod≤q) =
          isUpperSet≤ x ans (snd exi)
          where

          ans : xi-u ℚ≤ q
          ans = (handle2 (split-< xi-u 0r))
            where
            p1 = max (1i-l * xi-l) (1i-l * xi-u)
            p2 = max (1i-u * xi-l) (1i-u * xi-u)
            p0 = max p1 p2


            handle2 : (xi-u < 0r) ⊎ (0r ℚ≤ xi-u) -> xi-u ℚ≤ q
            handle2 (inj-l xi-u<0) =
              trans-ℚ≤ {xi-u} {p0} {q}
                (trans-ℚ≤ {xi-u} {p1} {p0}
                  (trans-ℚ≤ {xi-u} {p4} {p1} (weaken-< lt1) lt2)
                  lt3)
                prod≤q
              where
              p3 = (1i-l r* xi-l)
              p4 = (1i-l r* xi-u)


              lt1 : xi-u < (1i-l r* xi-u)
              lt1 = subst (_< (1i-l r* xi-u)) (r*-left-one xi-u)
                          (*₂-flips-< (L->ℚ< 1i-l<1) xi-u<0)

              lt2 : p4 ℚ≤ (max p3 p4)
              lt2 = max-≤-right
              lt3 : p1 ℚ≤ (max p1 p2)
              lt3 = max-≤-left

            handle2 (inj-r 0≤xi-u) =
              trans-ℚ≤ {xi-u} {p0} {q}
                (trans-ℚ≤ {xi-u} {p2} {p0}
                  (trans-ℚ≤ {xi-u} {p4} {p2} lt1 lt2)
                  lt3)
                prod≤q
              where
              p3 = (1i-u r* xi-l)
              p4 = (1i-u r* xi-u)

              lt1 : xi-u ℚ≤ (1i-u r* xi-u)
              lt1 = subst (_ℚ≤ (1i-u r* xi-u)) (r*-left-one xi-u)
                          (*₂-preserves-≤ (weaken-< (U->ℚ< 1<1i-u)) 0≤xi-u)
              lt2 : p4 ℚ≤ (max p3 p4)
              lt2 = max-≤-right
              lt3 : p2 ℚ≤ (max p1 p2)
              lt3 = max-≤-right


    ℝ*ᵉ-left-one : 1x == x
    ℝ*ᵉ-left-one = LU-paths->path 1x x L-path U-path

  abstract
    ℝ*-left-one : 1ℝ ℝ* x == x
    ℝ*-left-one = ℝ*ᵉ-left-one


module _ (x : ℝ)
  where
  private
    module x = Real x
    module 0ℝ = Real 0ℝ
    0x = 0ℝ ℝ*ᵉ x
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
          ∣ ir , ix , (ℚ<->L r<0 , ℚ<->U 0<mr) , (xl-p1 , xu-p2) , ans ∣
          where
          ix : Iℚ
          ix = ℝ-bounds->Iℚ x xl-p1 xu-p2

          m = i-maxabs ix

          0<m : 0# < m
          0<m = 0<i-maxabs ix

          inv-m = Pos->Inv 0<m
          1/m = (r1/ m inv-m)
          0<1/m = r1/-preserves-Pos m inv-m 0<m

          r = q r* 1/m

          q<0 = L->ℚ< 0ℝl-q

          r<0 = *₂-preserves-<0 q<0 0<1/m

          mr = r- r

          0<mr = minus-flips-<0 r<0
          r<mr = (trans-< r<0 0<mr)
          r≤mr = weaken-< r<mr

          ir = Iℚ-cons r mr r<mr

          m-ir = i-maxabs ir

          lb = Iℚ.l (ir i* ix)
          ub = Iℚ.u (ir i* ix)
          m2 = i-maxabs (ir i* ix)

          -lb≤m2 : (r- lb) ≤ m2
          -lb≤m2 = max-≤-left
          -m2≤lb : (r- m2) ≤ lb
          -m2≤lb = subst ((r- m2) ≤_) minus-double-inverse
                         (minus-flips-≤ -lb≤m2)

          m2=m-ir*m : m2 == m-ir r* m
          m2=m-ir*m = i-maxabs-i* ir ix

          m-ir=r : m-ir == (r- r)
          m-ir=r = max-idempotent

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
          ans = subst2 _ℚ≤_ path-q path-lb (minus-flips-≤ -lb≤-q)
            where
            path-lb : (r- (r- lb)) == lb
            path-lb = minus-double-inverse
            path-q : (r- (r- q)) == q
            path-q = minus-double-inverse


      i .fun 0x-q = unsquash (0ℝ.isProp-L q) (∥-map handle 0x-q)
        where
        handle : L' 0ℝ x q -> 0ℝ.L q
        handle (0i@(Iℚ-cons 0i-l 0i-u 0i-l≤u) , xi@(Iℚ-cons xi-l xi-u xi-l≤u) ,
                (0i-ll , 0i-uu) , exi , q≤prod) = ℚ<->L (trans-≤-< q≤prod p0<0)
          where
          l<0 : 0i-l < 0#
          l<0 = L->ℚ< 0i-ll
          0<u : 0# < 0i-u
          0<u = U->ℚ< 0i-uu

          p1 = min (0i-l * xi-l) (0i-l * xi-u)
          p2 = min (0i-u * xi-l) (0i-u * xi-u)
          p0 = min p1 p2

          p0<0 : p0 < 0#
          p0<0 = fst (i*₁-StrictCrossZero 0i xi (l<0 , 0<u))


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
          ∣ ir , ix , (ℚ<->L mr<0 , ℚ<->U 0<r) , (xl-p1 , xu-p2) , ub≤q ∣
          where
          ix : Iℚ
          ix = ℝ-bounds->Iℚ x xl-p1 xu-p2

          m = i-maxabs ix

          0<m : 0# < m
          0<m = 0<i-maxabs ix

          inv-m = Pos->Inv 0<m
          1/m = (r1/ m inv-m)
          0<1/m = r1/-preserves-Pos m inv-m 0<m

          r = q r* 1/m

          0<q = U->ℚ< 0ℝu-q

          0<r = *-preserves-0< 0<q 0<1/m

          mr = r- r

          mr<0 = minus-flips-0< 0<r
          mr<r = trans-< mr<0 0<r
          mr≤r = weaken-< mr<r

          ir = Iℚ-cons mr r mr<r

          m-ir = i-maxabs ir

          lb = Iℚ.l (ir i* ix)
          ub = Iℚ.u (ir i* ix)
          m2 = i-maxabs (ir i* ix)

          ub≤m2 : ub ≤ m2
          ub≤m2 = max-≤-right

          m2=m-ir*m : m2 == m-ir r* m
          m2=m-ir*m = i-maxabs-i* ir ix

          m-ir=r : m-ir == r
          m-ir=r = cong (\x -> max x r) minus-double-inverse >=>
                   max-idempotent

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
                (0i-ll , 0i-uu) , exi , prod≤q) = ℚ<->U (trans-<-≤ 0<p0 prod≤q)
          where
          l<0 : 0i-l < 0#
          l<0 = L->ℚ< 0i-ll
          0<u : 0# < 0i-u
          0<u = U->ℚ< 0i-uu

          p1 = max (0i-l * xi-l) (0i-l * xi-u)
          p2 = max (0i-u * xi-l) (0i-u * xi-u)
          p0 = max p1 p2

          0<p0 : 0# < p0
          0<p0 = snd (i*₁-StrictCrossZero 0i xi (l<0 , 0<u))

    ℝ*ᵉ-left-zero : 0x == 0ℝ
    ℝ*ᵉ-left-zero = LU-paths->path 0x 0ℝ L-path U-path

  abstract
    ℝ*-left-zero : 0ℝ ℝ* x == 0ℝ
    ℝ*-left-zero = ℝ*ᵉ-left-zero

-- Interval properties
abstract
  ℝ∈Iℚ-*ᵉ : (x y : ℝ) (a b : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ y b -> ℝ∈Iℚ (x ℝ*ᵉ y) (a i* b)
  ℝ∈Iℚ-*ᵉ x y a b x∈a y∈b = ∣ a , b , x∈a , y∈b , refl-ℚ≤ ∣ , ∣ a , b , x∈a , y∈b , refl-ℚ≤ ∣

  ℝ∈Iℚ-* : (x y : ℝ) (a b : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ y b -> ℝ∈Iℚ (x ℝ* y) (a i* b)
  ℝ∈Iℚ-* x y a b x∈a y∈b =
    subst (\z -> ℝ∈Iℚ z (a i* b)) (sym (ℝ*-eval {x} {y})) (ℝ∈Iℚ-*ᵉ x y a b x∈a y∈b)

  ℝ∈Iℚ-*ᵉ⁻ : (x y : ℝ) (a : Iℚ) -> ℝ∈Iℚ (x ℝ*ᵉ y) a ->
            ∥ Σ[ b ∈ Iℚ ] Σ[ c ∈ Iℚ ] (ℝ∈Iℚ x b × ℝ∈Iℚ y c × (b i* c) i⊆ a) ∥
  ℝ∈Iℚ-*ᵉ⁻ x y a@(Iℚ-cons al au al≤au) (xyl-al , xyu-au) = (∥-map2 handle xyl-al xyu-au)
    where
    handle : L' x y al -> U' x y au -> Σ[ b ∈ Iℚ ] Σ[ c ∈ Iℚ ] (ℝ∈Iℚ x b × ℝ∈Iℚ y c × (b i* c) i⊆ a)
    handle (bi , ci , x∈b , y∈c , al≤bc) (di , ei , x∈d , y∈e , de≤au) =
      xi , yi , x∈xi , y∈yi , (i⊆-cons al≤xiyi xiyi≤au)
      where
      module _ where
        o-bd = ℝ∈Iℚ->Overlap x bi di x∈b x∈d
        xi = i-intersect bi di o-bd
        x∈xi = ℝ∈Iℚ-intersect x bi di x∈b x∈d

        o-ce = ℝ∈Iℚ->Overlap y ci ei y∈c y∈e
        yi = i-intersect ci ei o-ce
        y∈yi = ℝ∈Iℚ-intersect y ci ei y∈c y∈e

        xi⊆bi = i-intersect-⊆₁ bi di o-bd
        xi⊆di = i-intersect-⊆₂ bi di o-bd
        yi⊆ci = i-intersect-⊆₁ ci ei o-ce
        yi⊆ei = i-intersect-⊆₂ ci ei o-ce

        xiyi⊆bc = i*-preserves-⊆ xi⊆bi yi⊆ci
        xiyi⊆de = i*-preserves-⊆ xi⊆di yi⊆ei

        al≤xiyi = i⊆-Lower xiyi⊆bc al al≤bc
        xiyi≤au = i⊆-Upper xiyi⊆de au de≤au

  ℝ∈Iℚ-*⁻ : (x y : ℝ) (a : Iℚ) -> ℝ∈Iℚ (x ℝ* y) a ->
            ∥ Σ[ b ∈ Iℚ ] Σ[ c ∈ Iℚ ] (ℝ∈Iℚ x b × ℝ∈Iℚ y c × (b i* c) i⊆ a) ∥
  ℝ∈Iℚ-*⁻ x y a xy∈a =
    ℝ∈Iℚ-*ᵉ⁻ x y a (subst (\z -> ℝ∈Iℚ z a) (ℝ*-eval {x} {y}) xy∈a)
