{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic where

open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-<)
open import real
open import real.sequence
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation
open import univalence

module _ (x y : ℝ) where
  private
    module x = Real x
    module y = Real y

    L' : Pred ℚ ℓ-zero
    L' q = Σ[ r1 ∈ ℚ ] (Σ[ r2 ∈ ℚ ] (x.L r1 × y.L r2 × r1 r+ r2 == q))
    U' : Pred ℚ ℓ-zero
    U' q = Σ[ r1 ∈ ℚ ] (Σ[ r2 ∈ ℚ ] (x.U r1 × y.U r2 × r1 r+ r2 == q))

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥
    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-map2 handle x.Inhabited-L y.Inhabited-L
      where
      handle : Σ ℚ x.L -> Σ ℚ y.L -> Σ ℚ L
      handle (r1 , l-r1) (r2 , l-r2) =
        (r1 r+ r2 , ∣ (r1 , r2 , l-r1 , l-r2 , refl) ∣)

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map2 handle x.Inhabited-U y.Inhabited-U
      where
      handle : Σ ℚ x.U -> Σ ℚ y.U -> Σ ℚ U
      handle (r1 , u-r1) (r2 , u-r2) =
        (r1 r+ r2 , ∣ (r1 , r2 , u-r1 , u-r2 , refl) ∣)

    isLowerSet-L : isLowerSet L
    isLowerSet-L a b a<b = ∥-map handle
      where
      handle : L' b -> L' a
      handle (r1 , r2 , l-r1 , l-r2 , r-path) =
        (r1 , r3 , l-r1 , y.isLowerSet-L r3 r2 r3<r2 l-r2 , r3-path)
        where
        r3 = r2 r+ (diffℚ b a)
        r3<r2 : r3 < r2
        r3<r2 = r+-Neg->order r2 ((diffℚ b a) ,
                                  subst Neg (sym (diffℚ-anticommute b a))
                                        (r--flips-sign (diffℚ a b) pos-sign a<b))
        r3-path : r1 r+ r3 == a
        r3-path =
          sym (r+-assoc r1 r2 (a r+ (r- b))) >=>
          cong2 _r+_ r-path (r+-commute a (r- b)) >=>
          sym (r+-assoc b (r- b) a) >=>
          cong (_r+ a) (r+-inverse b) >=>
          r+-left-zero a

    isUpperSet-U : isUpperSet U
    isUpperSet-U a b a<b = ∥-map handle
      where
      handle : U' a -> U' b
      handle (r1 , r2 , l-r1 , l-r2 , r-path) =
        (r1 , r3 , l-r1 , y.isUpperSet-U r2 r3 r2<r3 l-r2 , r3-path)
        where
        r3 = r2 r+ (diffℚ a b)
        r2<r3 : r2 < r3
        r2<r3 = r+-Pos->order r2 ((diffℚ a b) , a<b)
        r3-path : r1 r+ r3 == b
        r3-path =
          sym (r+-assoc r1 r2 (b r+ (r- a))) >=>
          cong2 _r+_ r-path (r+-commute b (r- a)) >=>
          sym (r+-assoc a (r- a) b) >=>
          cong (_r+ b) (r+-inverse a) >=>
          r+-left-zero b


    disjoint : Universal (Comp (L ∩ U))
    disjoint a (l-a , u-a) = unsquash isPropBot (∥-map2 handle l-a u-a)
      where
      handle : L' a -> U' a -> Bot
      handle (r1 , r2 , l-r1 , l-r2 , r12-path) (r3 , r4 , u-r3 , u-r4 , r34-path) =
        handle2 (trichotomous-< r1 r3) (trichotomous-< r2 r4)
        where
        handle2 : (Tri (r1 < r3) (r1 == r3) (r1 > r3)) -> (Tri (r2 < r4) (r2 == r4) (r2 > r4)) -> Bot
        handle2 (tri< r1<r3 _ _) (tri< r2<r4 _ _) =
          irrefl-< {a = r3 r+ r4} (subst (_< (r3 r+ r4)) (r12-path >=> sym (r34-path))
                                         (r+-both-preserves-order r1 r3 r2 r4 r1<r3 r2<r4))
        handle2 (tri< _ _ _) (tri= _ r2==r4 _) =
          y.disjoint r4 ((subst y.L r2==r4 l-r2) , u-r4)
        handle2 (tri< _ _ _) (tri> _ _ r4<r2) =
          y.disjoint r4 ((y.isLowerSet-L r4 r2 r4<r2 l-r2) , u-r4)
        handle2 (tri= _ r1==r3 _) _ =
          x.disjoint r3 ((subst x.L r1==r3 l-r1) , u-r3)
        handle2 (tri> _ _ r3<r1) _ =
          x.disjoint r3 ((x.isLowerSet-L r3 r1 r3<r1 l-r1) , u-r3)

    located : (a b : ℚ) -> a < b -> ∥ L a ⊎ U b ∥
    located a b a<b = ∥-bind handle (find-centered-ball x ε)
      where
      s = seperate-< a b a<b
      ε : ℚ⁺
      ε = fst s
      ε' : ℚ
      ε' = fst ε
      aε<bε : (a r+ ε') < (b r+ (r- ε'))
      aε<bε = snd s

      handle : Σ[ c ∈ ℚ ] (x.L (c r+ (r- ε')) × x.U (c r+ ε')) -> ∥ L a ⊎ U b ∥
      handle (c , Lc⁻ , Uc⁺) = ∥-map handle2 (y.located d e d<e)
        where
        c⁻ = c r+ (r- ε')
        c⁺ = c r+ ε'

        d = a r+ (r- c⁻)
        e = b r+ (r- c⁺)
        d<e : d < e
        d<e = subst2 _<_ path1 path2 (r+₂-preserves-order (a r+ ε') (b r+ (r- ε')) (r- c) aε<bε)
          where
          path1 : (a r+ ε') r+ (r- c) == d
          path1 = r+-assoc a ε' (r- c) >=> cong (a r+_) (diffℚ-anticommute c ε')
          path2 : (b r+ (r- ε')) r+ (r- c) == e
          path2 = r+-assoc b (r- ε') (r- c) >=>
                  cong (b r+_) (sym (RationalRing.minus-distrib-plus {ε'} {c}) >=>
                                cong r-_ (r+-commute ε' c))

        d-path : c⁻ r+ d == a
        d-path = diffℚ-step c⁻ a
        e-path : c⁺ r+ e == b
        e-path = diffℚ-step c⁺ b

        handle2 : y.L d ⊎ y.U e -> L a ⊎ U b
        handle2 (inj-l Ld) = inj-l ∣ c⁻ , d , Lc⁻ , Ld , d-path ∣
        handle2 (inj-r Ue) = inj-r ∣ c⁺ , e , Uc⁺ , Ue , e-path ∣

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' q -> ∃[ r ∈ ℚ ] (q < r × L r)
      handle (a , b , la , lb , p) = ∥-map handle2 (x.isUpperOpen-L a la)
        where
        handle2 : Σ[ c ∈ ℚ ] (a < c × x.L c) -> Σ[ r ∈ ℚ ] (q < r × L r)
        handle2 (c , a<c , lc) = (c r+ b , lt , ∣ c , b , lc , lb , refl ∣)
          where
          lt : q < (c r+ b)
          lt = subst (_< (c r+ b)) p (r+₂-preserves-order a c b a<c)

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-bind handle
      where
      handle : U' q -> ∃[ r ∈ ℚ ] (r < q × U r)
      handle (a , b , ua , ub , p) = ∥-map handle2 (x.isLowerOpen-U a ua)
        where
        handle2 : Σ[ c ∈ ℚ ] (c < a × x.U c) -> Σ[ r ∈ ℚ ] (r < q × U r)
        handle2 (c , c<a , uc) = (c r+ b , lt , ∣ c , b , uc , ub , refl ∣)
          where
          lt : (c r+ b) < q
          lt = subst ((c r+ b) <_) p (r+₂-preserves-order c a b c<a)

  _ℝ+_ : ℝ
  _ℝ+_ = record
    { L = L
    ; U = U
    ; isProp-L = \q -> squash
    ; isProp-U = \q -> squash
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
    xy = x ℝ+ y
    yx = y ℝ+ x
    module xy = Real xy
    module yx = Real yx

    L-path : (q : ℚ) -> xy.L q == yx.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (xy.L q) (yx.L q)
      i .fun = ∥-map handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.L a × y.L b × (a r+ b) == q) ->
                 Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (y.L a × x.L b × (a r+ b) == q)
        handle (a , b , la , lb , p) = b , a , lb , la , r+-commute b a >=> p
      i .inv = ∥-map handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (y.L a × x.L b × (a r+ b) == q) ->
                 Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.L a × y.L b × (a r+ b) == q)
        handle (a , b , la , lb , p) = b , a , lb , la , r+-commute b a >=> p
      i .rightInv _ = squash _ _
      i .leftInv _ = squash _ _

    U-path : (q : ℚ) -> xy.U q == yx.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (xy.U q) (yx.U q)
      i .fun = ∥-map handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.U a × y.U b × (a r+ b) == q) ->
                 Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (y.U a × x.U b × (a r+ b) == q)
        handle (a , b , ua , ub , p) = b , a , ub , ua , r+-commute b a >=> p
      i .inv = ∥-map handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (y.U a × x.U b × (a r+ b) == q) ->
                 Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.U a × y.U b × (a r+ b) == q)
        handle (a , b , ua , ub , p) = b , a , ub , ua , r+-commute b a >=> p
      i .rightInv _ = squash _ _
      i .leftInv _ = squash _ _

  ℝ+-commute : xy == yx
  ℝ+-commute = LU-paths->path xy yx L-path U-path
