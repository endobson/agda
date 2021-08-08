{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic where

open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import ordered-semiring
open import ordered-ring
open import order.instances.rational
open import rational
open import rational.difference
open import rational.order
open import rational.proper-interval
open import real
open import real.interval
open import real.sequence
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import sum
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
                                        (r--flips-sign (diffℚ a b) pos-sign (Pos-diffℚ a b a<b)))
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
        r2<r3 = r+-Pos->order r2 ((diffℚ a b) , (Pos-diffℚ a b a<b))
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
                                         (+-preserves-< r1 r3 r2 r4 r1<r3 r2<r4))
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
        d<e = subst2 _<_ path1 path2 (+₂-preserves-< (a r+ ε') (b r+ (r- ε')) (r- c) aε<bε)
          where
          path1 : (a r+ ε') r+ (r- c) == d
          path1 = r+-assoc a ε' (r- c) >=> cong (a r+_) (diffℚ-anticommute c ε')
          path2 : (b r+ (r- ε')) r+ (r- c) == e
          path2 = r+-assoc b (r- ε') (r- c) >=>
                  cong (b r+_) (sym minus-distrib-plus >=>
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
          lt = subst (_< (c r+ b)) p (+₂-preserves-< a c b a<c)

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
          lt = subst ((c r+ b) <_) p (+₂-preserves-< c a b c<a)

  _ℝ+ᵉ_ : ℝ
  _ℝ+ᵉ_ = record
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


abstract
  _ℝ+_ : ℝ -> ℝ -> ℝ
  a ℝ+ b = a ℝ+ᵉ b

  ℝ+-eval : {a b : ℝ} -> a ℝ+ b == a ℝ+ᵉ b
  ℝ+-eval = refl


module _ (x y : ℝ) where
  private
    module x = Real x
    module y = Real y
    xy = x ℝ+ᵉ y
    yx = y ℝ+ᵉ x
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

    ℝ+ᵉ-commute : xy == yx
    ℝ+ᵉ-commute = LU-paths->path xy yx L-path U-path

  abstract
    ℝ+-commute : x ℝ+ y == y ℝ+ x
    ℝ+-commute = ℝ+ᵉ-commute



module _ (x y z : ℝ) where
  private
    module x = Real x
    module y = Real y
    module z = Real z
    xy = x ℝ+ᵉ y
    xy-z = xy ℝ+ᵉ z
    yz = y ℝ+ᵉ z
    x-yz = x ℝ+ᵉ yz

    module xy = Real xy
    module xy-z = Real xy-z
    module yz = Real yz
    module x-yz = Real x-yz

    L-path : (q : ℚ) -> xy-z.L q == x-yz.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (xy-z.L q) (x-yz.L q)
      i .rightInv _ = squash _ _
      i .leftInv _ = squash _ _
      i .fun = ∥-bind handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (xy.L a × z.L b × (a r+ b) == q) ->
                 ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.L a × yz.L b × (a r+ b) == q)
        handle (a , b , xyl-a , zl-b , ab=q) = ∥-bind handle2 xyl-a
          where
          handle2 : Σ[ c ∈ ℚ ] Σ[ d ∈ ℚ ] (x.L c × y.L d × (c r+ d) == a) ->
                    ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.L a × yz.L b × (a r+ b) == q)
          handle2 (c , d , xl-c , yl-d , cd=a) =
            ∣ (c , d r+ b , xl-c , ∣ (d , b , yl-d , zl-b , refl) ∣ , path) ∣
            where
            path : c r+ (d r+ b) == q
            path = sym (r+-assoc c d b) >=> cong (_r+ b) cd=a >=> ab=q
      i .inv = ∥-bind handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.L a × yz.L b × (a r+ b) == q) ->
                 ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (xy.L a × z.L b × (a r+ b) == q)
        handle (a , b , xl-a , yzl-b , ab=q) = ∥-bind handle2 yzl-b
          where
          handle2 : Σ[ c ∈ ℚ ] Σ[ d ∈ ℚ ] (y.L c × z.L d × (c r+ d) == b) ->
                    ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (xy.L a × z.L b × (a r+ b) == q)
          handle2 (c , d , yl-c , zl-d , cd=b) =
            ∣ (a r+ c , d , ∣ (a , c , xl-a , yl-c , refl) ∣ , zl-d , path) ∣
            where
            path : (a r+ c) r+ d == q
            path = (r+-assoc a c d) >=> cong (a r+_) cd=b >=> ab=q

    U-path : (q : ℚ) -> xy-z.U q == x-yz.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (xy-z.U q) (x-yz.U q)
      i .rightInv _ = squash _ _
      i .leftInv _ = squash _ _
      i .fun = ∥-bind handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (xy.U a × z.U b × (a r+ b) == q) ->
                 ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.U a × yz.U b × (a r+ b) == q)
        handle (a , b , xyu-a , zu-b , ab=q) = ∥-bind handle2 xyu-a
          where
          handle2 : Σ[ c ∈ ℚ ] Σ[ d ∈ ℚ ] (x.U c × y.U d × (c r+ d) == a) ->
                    ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.U a × yz.U b × (a r+ b) == q)
          handle2 (c , d , xu-c , yu-d , cd=a) =
            ∣ (c , d r+ b , xu-c , ∣ (d , b , yu-d , zu-b , refl) ∣ , path) ∣
            where
            path : c r+ (d r+ b) == q
            path = sym (r+-assoc c d b) >=> cong (_r+ b) cd=a >=> ab=q
      i .inv = ∥-bind handle
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (x.U a × yz.U b × (a r+ b) == q) ->
                 ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (xy.U a × z.U b × (a r+ b) == q)
        handle (a , b , xu-a , yzu-b , ab=q) = ∥-bind handle2 yzu-b
          where
          handle2 : Σ[ c ∈ ℚ ] Σ[ d ∈ ℚ ] (y.U c × z.U d × (c r+ d) == b) ->
                    ∃[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (xy.U a × z.U b × (a r+ b) == q)
          handle2 (c , d , yu-c , zu-d , cd=b) =
            ∣ (a r+ c , d , ∣ (a , c , xu-a , yu-c , refl) ∣ , zu-d , path) ∣
            where
            path : (a r+ c) r+ d == q
            path = (r+-assoc a c d) >=> cong (a r+_) cd=b >=> ab=q

    ℝ+ᵉ-assoc : xy-z == x-yz
    ℝ+ᵉ-assoc = LU-paths->path xy-z x-yz L-path U-path

  abstract
    ℝ+-assoc : (x ℝ+ y) ℝ+ z == x ℝ+ (y ℝ+ z)
    ℝ+-assoc = ℝ+ᵉ-assoc


module _ (x : ℝ) where
  private
    module x = Real x
    module 0ℝ = Real 0ℝ
    0x = 0ℝ ℝ+ᵉ x
    module 0x = Real 0x

    L-path : (q : ℚ) -> 0x.L q == x.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (0x.L q) (x.L q)
      i .rightInv _ = x.isProp-L q _ _
      i .leftInv _ = 0x.isProp-L q _ _
      i .inv xl-q = ∥-bind handle (x.isUpperOpen-L q xl-q)
        where
        handle : Σ[ r ∈ ℚ ] (q < r × x.L r) -> 0x.L q
        handle (r , q<r , xl-r) = ∣ (diffℚ r q) , r , d<0 , xl-r , path ∣
          where
          path : (diffℚ r q) r+ r == q
          path = r+-commute (diffℚ r q) r >=> diffℚ-step r q

          d'>0 : (diffℚ q r) > 0r
          d'>0 = Pos-diffℚ q r q<r

          d<0 : (diffℚ r q) < 0r
          d<0 = subst (_< 0r) (sym (diffℚ-anticommute r q)) (minus-flips-0< d'>0)

      i .fun 0xl-q = unsquash (x.isProp-L q) (∥-map handle 0xl-q)
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (0ℝ.L a × x.L b × a r+ b == q) -> x.L q
        handle (a , b , 0l-a , xl-b , p) = x.isLowerSet-L q b q<b xl-b
          where
          q<b : q < b
          q<b = subst2 _<_ p (r+-left-zero b) (+₂-preserves-< a 0r b 0l-a)

    U-path : (q : ℚ) -> 0x.U q == x.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (0x.U q) (x.U q)
      i .rightInv _ = x.isProp-U q _ _
      i .leftInv _ = 0x.isProp-U q _ _
      i .inv xu-q = ∥-bind handle (x.isLowerOpen-U q xu-q)
        where
        handle : Σ[ r ∈ ℚ ] (r < q × x.U r) -> 0x.U q
        handle (r , r<q , xu-r) = ∣ (diffℚ r q) , r , 0<d , xu-r , path ∣
          where
          path : (diffℚ r q) r+ r == q
          path = r+-commute (diffℚ r q) r >=> diffℚ-step r q

          0<d : 0r < (diffℚ r q)
          0<d = Pos-diffℚ r q r<q
      i .fun 0xu-q = unsquash (x.isProp-U q) (∥-map handle 0xu-q)
        where
        handle : Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] (0ℝ.U a × x.U b × a r+ b == q) -> x.U q
        handle (a , b , 0u-a , xu-b , p) = x.isUpperSet-U b q b<q xu-b
          where
          b<q : b < q
          b<q = subst2 _<_ (r+-left-zero b) p (+₂-preserves-< 0r a b 0u-a)

    ℝ+ᵉ-left-zero : 0x == x
    ℝ+ᵉ-left-zero = LU-paths->path 0x x L-path U-path

  abstract
    ℝ+-left-zero : 0ℝ ℝ+ x == x
    ℝ+-left-zero = ℝ+ᵉ-left-zero

module _ (x : ℝ) where
  private
    module x = Real x

    L : Pred ℚ ℓ-zero
    L q = x.U (r- q)
    U : Pred ℚ ℓ-zero
    U q = x.L (r- q)

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-map handle x.Inhabited-U
      where
      handle : Σ[ q ∈ ℚ ] (x.U q) -> Σ ℚ L
      handle (q , uq) = (r- q) , subst x.U (sym minus-double-inverse) uq

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map handle x.Inhabited-L
      where
      handle : Σ[ q ∈ ℚ ] (x.L q) -> Σ ℚ U
      handle (q , lq) = (r- q) , subst x.L (sym minus-double-inverse) lq

    isLowerSet-L : isLowerSet L
    isLowerSet-L a b a<b = x.isUpperSet-U (r- b) (r- a) (minus-flips-< a b a<b)
    isUpperSet-U : isUpperSet U
    isUpperSet-U a b a<b = x.isLowerSet-L (r- b) (r- a) (minus-flips-< a b a<b)

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q lq = ∥-map handle (x.isLowerOpen-U (r- q) lq)
      where
      handle : Σ[ r ∈ ℚ ] (r < (r- q) × x.U r) ->
               Σ[ r ∈ ℚ ] (q < r × L r)
      handle (r , r<-q , ur) =
        (r- r) ,
        Pos-diffℚ⁻ q (r- r) (subst Pos (r+-commute (r- q) (r- r)) (Pos-diffℚ r (- q) r<-q)),
        subst x.U (sym minus-double-inverse) ur

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q uq = ∥-map handle (x.isUpperOpen-L (r- q) uq)
      where
      handle : Σ[ r ∈ ℚ ] ((r- q) < r × x.L r) ->
               Σ[ r ∈ ℚ ] (r < q × U r)
      handle (r , -q<r , lr) =
        (r- r) ,
        Pos-diffℚ⁻ (r- r) q (subst Pos path (Pos-diffℚ (- q) r -q<r)) ,
        subst x.L (sym minus-double-inverse) lr
        where
        path : r r+ (r- (r- q)) == q r+ (r- (r- r))
        path = cong (r r+_) minus-double-inverse >=>
               r+-commute r q >=>
               cong (q r+_) (sym minus-double-inverse)

    disjoint : Universal (Comp (L ∩ U))
    disjoint q (lq , uq) = x.disjoint (r- q) (uq , lq)

    located : (a b : ℚ) -> a < b -> ∥ L a ⊎ U b ∥
    located a b a<b = ∥-map ⊎-swap (x.located (r- b) (r- a) (minus-flips-< a b a<b))

  ℝ-ᵉ_ : ℝ
  ℝ-ᵉ_ = record
    { L = L
    ; U = U
    ; isProp-L = \q -> x.isProp-U (r- q)
    ; isProp-U = \q -> x.isProp-L (r- q)
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
  ℝ-_ : ℝ -> ℝ
  ℝ- a = ℝ-ᵉ a

  ℝ--eval : {a : ℝ} -> ℝ- a == ℝ-ᵉ a
  ℝ--eval = refl

module _ (x : ℝ) where
  private
    -x = ℝ-ᵉ x
    y = x ℝ+ᵉ -x
    module -x = Real -x
    module x = Real x
    module y = Real y
    module 0ℝ = Real 0ℝ

    L-forward : (q : ℚ) -> y.L q -> 0ℝ.L q
    L-forward q yl-q = unsquash (0ℝ.isProp-L q) (∥-map handle yl-q)
      where
      handle : Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (x.L q1 × x.U (r- q2) × q1 r+ q2 == q) ->
               q < 0r
      handle (q1 , q2 , xl-q1 , xu-mq2 , q-path) = q<0r
        where
        q1<mq2 : q1 < (r- q2)
        q1<mq2 = ℝ-bounds->ℚ< x q1 (r- q2) xl-q1 xu-mq2

        q<0r : q < 0r
        q<0r =
          Pos-diffℚ⁻ q 0r
            (subst Pos (sym minus-distrib-plus >=>
                        cong r-_ (r+-commute q2 q1 >=> q-path) >=>
                        sym (r+-left-zero (r- q)))
                   (Pos-diffℚ q1 (- q2) q1<mq2))

    L-backward : (q : ℚ) -> 0ℝ.L q -> y.L q
    L-backward q q<0r = ∥-map handle (find-open-ball x -q)
      where
      -q' = r- q
      -q : ℚ⁺
      -q = -q' , subst Pos (r+-left-zero -q') (Pos-diffℚ q 0r q<0r)

      handle :  Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (Real.L x q1 × Real.U x q2 × diffℚ q1 q2 == -q') ->
                Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (x.L q1 × x.U (r- q2) × q1 r+ q2 == q)
      handle (q1 , q2 , xl-q1 , xu-q2 , diff-path) = q1 , (r- q2) , xl-q1 , xu-mmq2 , path
        where
        xu-mmq2 : x.U (r- (r- q2))
        xu-mmq2 = subst x.U (sym minus-double-inverse) xu-q2

        path : diffℚ q2 q1 == q
        path = diffℚ-anticommute q2 q1 >=> cong r-_ diff-path >=> minus-double-inverse

    U-forward : (q : ℚ) -> y.U q -> 0ℝ.U q
    U-forward q yu-q = unsquash (0ℝ.isProp-U q) (∥-map handle yu-q)
      where
      handle : Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (x.U q1 × x.L (r- q2) × q1 r+ q2 == q) ->
               0r < q
      handle (q1 , q2 , xu-q1 , xl-mq2 , q-path) = 0r<q
        where
        mq2<q1 : (r- q2) < q1
        mq2<q1 = ℝ-bounds->ℚ< x (r- q2) q1 xl-mq2 xu-q1

        0r<q : 0r < q
        0r<q = Pos-0< q (subst Pos (cong (q1 r+_) minus-double-inverse >=> q-path)
                                   (Pos-diffℚ (- q2) q1 mq2<q1))

    U-backward : (q : ℚ) -> 0ℝ.U q -> y.U q
    U-backward q 0r<q = ∥-map handle (find-open-ball x q⁺)
      where
      q⁺ : ℚ⁺
      q⁺ = q , 0r<q

      handle :  Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (Real.L x q1 × Real.U x q2 × diffℚ q1 q2 == q) ->
                Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (x.U q1 × x.L (r- q2) × q1 r+ q2 == q)
      handle (q1 , q2 , xl-q1 , xu-q2 , path) = q2 , (r- q1) , xu-q2 , xl-mmq1 , path
        where
        xl-mmq1 : x.L (r- (r- q1))
        xl-mmq1 = subst x.L (sym minus-double-inverse) xl-q1

    ℝ+ᵉ-inverse : y == 0ℝ
    ℝ+ᵉ-inverse =
      LU-paths->path y 0ℝ
        (\q -> (ua (isoToEquiv (isProp->iso (L-forward q) (L-backward q)
                                            (y.isProp-L q) (0ℝ.isProp-L q)))))
        (\q -> (ua (isoToEquiv (isProp->iso (U-forward q) (U-backward q)
                                            (y.isProp-U q) (0ℝ.isProp-U q)))))

  abstract
    ℝ+-inverse : (x ℝ+ (ℝ- x)) == 0ℝ
    ℝ+-inverse = ℝ+ᵉ-inverse


-- Interval arithmetic

-- ℝ∈Iℚ-+ : (x y : ℝ) (a b : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ y b -> ℝ∈Iℚ (x ℝ+ y) (a i+ b)
-- ℝ∈Iℚ-+ x y a b (xl-a , xu-a) (yl-b , yu-b) =
--   ∣ Iℚ.l a , Iℚ.l b , xl-a , yl-b , refl ∣ ,
--   ∣ Iℚ.u a , Iℚ.u b , xu-a , yu-b , refl ∣


ℝ∈Iℚ-+ᵉ : (x y : ℝ) (a b : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ y b -> ℝ∈Iℚ (x ℝ+ᵉ y) (a i+ b)
ℝ∈Iℚ-+ᵉ x y a b (xl-a , xu-a) (yl-b , yu-b) =
  ∣ Iℚ.l a , Iℚ.l b , xl-a , yl-b , refl ∣ ,
  ∣ Iℚ.u a , Iℚ.u b , xu-a , yu-b , refl ∣

abstract
  ℝ∈Iℚ--ᵉ : (x : ℝ) (a : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ (ℝ-ᵉ x) (i- a)
  ℝ∈Iℚ--ᵉ x a (xl-a , xu-a) = (subst x.U (sym minus-double-inverse) xu-a ,
                               subst x.L (sym minus-double-inverse) xl-a)
    where
    module x = Real x

  ℝ∈Iℚ-- : (x : ℝ) (a : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ (ℝ- x) (i- a)
  ℝ∈Iℚ-- = ℝ∈Iℚ--ᵉ
