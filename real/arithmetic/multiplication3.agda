{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication3 where

open import base
open import equality
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
open import real.arithmetic.absolute-value
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation

module _ (x y : ℝ)
  where
  private
    module x = Real x
    module y = Real y

    ℝ∈Iℚ : ℝ -> Iℚ -> Type₀
    ℝ∈Iℚ z (Iℚ-cons l u _) = Real.L z l × Real.U z u

    L' : Pred ℚ ℓ-zero
    L' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Lower (xi i* yi) q)

    U' : Pred ℚ ℓ-zero
    U' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Upper (xi i* yi) q)

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥
    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥

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
      handle : L' b -> L' a
      handle (xi , yi , exi , eyi , lt) =
        (xi , yi , exi , eyi , inj-l (trans-<-≤ {a} {b} {Iℚ.l (xi i* yi)} a<b lt))

    isUpperSet-U : isUpperSet U
    isUpperSet-U a b a<b = ∥-map handle
      where
      handle : U' a -> U' b
      handle (xi , yi , exi , eyi , lt) =
        (xi , yi , exi , eyi , inj-l (trans-≤-< {Iℚ.u (xi i* yi)} {a} {b} lt a<b))


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' q -> ∃[ r ∈ ℚ ] (q < r × L r)
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
      handle : U' q -> ∃[ r ∈ ℚ ] (r < q × U r)
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
      handle : L' q -> U' q -> Bot
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

  module _
    (located : (a b : ℚ) -> a < b -> ∥ L a ⊎ U b ∥)
    where
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
