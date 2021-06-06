{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic where

open import base
open import equality
open import hlevel
open import real
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-<)
open import relation hiding (U)
open import sign
open import truncation
open import order
open import order.instances.rational

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

    -- located : (a b : ℚ) -> a < b -> ∥ L a ⊎ U b ∥
    -- located a b a<b = ∥-map2 handle (x.located a' b' a'<b') (y.located a' b' a'<b')
    --   where
    --   a' = 1/2r r* a
    --   b' = 1/2r r* b
    --   a'<b' : a' < b'
    --   a'<b' = ?

    --   module _ (z : ℝ) where
    --     module z = Real z


    --   handle : x.L a' ⊎ x.U b' -> y.L a' ⊎ y.U b' -> L a ⊎ U b
    --   handle (inj-l xl-a) (inj-l yl-a) = inj-l ∣ a' , a' , xl-a , yl-a , 1/2r-path' a ∣
    --   handle (inj-l xl-a) (inj-r yu-b) = ?
    --   handle (inj-r xu-b) (inj-l yl-a) = ?
    --   handle (inj-r xu-b) (inj-r yu-b) = inj-r ∣ b' , b' , xu-b , yu-b , 1/2r-path' b ∣




  -- _ℝ+_ : ℝ
  -- _ℝ+_ = record
  --   { L = L
  --   ; U = U
  --   ; isProp-L = \q -> squash
  --   ; isProp-U = \q -> squash
  --   ; Inhabited-L = Inhabited-L
  --   ; Inhabited-U = Inhabited-U
  --   ; isLowerSet-L = isLowerSet-L
  --   ; isUpperSet-U = isUpperSet-U
  --   ; isUpperOpen-L = ? -- isUpperOpen-L
  --   ; isLowerOpen-U = ? -- isLowerOpen-U
  --   ; disjoint = disjoint
  --   ; located = located
  --   }
