{-# OPTIONS --cubical --safe --exact-split #-}

module real.maximum where

open import real
open import base
open import hlevel
open import truncation
open import relation hiding (U)
open import rational
open import rational.proper-interval
open import rational.order
open import real.interval
open import real.rational
open import real.order
open import order
open import order.minmax
open import order.minmax.instances.rational
open import order.instances.real
open import sum
open import order.instances.rational

module _ (a b : ℝ) where
  private
    module a = Real a
    module b = Real b
    L' : Pred ℚ ℓ-zero
    L' q = a.L q ⊎ b.L q

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥

    U : Pred ℚ ℓ-zero
    U q = a.U q × b.U q

    Inhabited-L : ∃ ℚ L
    Inhabited-L = ∥-map (\(q , u) -> q , ∣ inj-l u ∣) a.Inhabited-L

    Inhabited-U : ∃ ℚ U
    Inhabited-U = ∥-map2 handle a.Inhabited-U b.Inhabited-U
      where
      handle : Σ ℚ a.U -> Σ ℚ b.U -> Σ ℚ U
      handle (q1 , aU-q1) (q2 , bU-q2) =
        max q1 q2 , (isUpperSet≤ a max-≤-left aU-q1 , isUpperSet≤ b max-≤-right bU-q2)

    isUpperSet-U : isUpperSet U
    isUpperSet-U q<r (aU-q , bU-q) =
      (a.isUpperSet-U q<r aU-q , b.isUpperSet-U q<r bU-q)

    isLowerSet-L : isLowerSet L
    isLowerSet-L q<r =
      ∥-map (⊎-map (a.isLowerSet-L q<r) (b.isLowerSet-L q<r))


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q (aU-q , bU-q) =
      ∥-map2 handle (a.isLowerOpen-U q aU-q) (b.isLowerOpen-U q bU-q)
      where
      handle : Σ[ r1 ∈ ℚ ] (r1 < q × a.U r1) -> Σ[ r2 ∈ ℚ ] (r2 < q × b.U r2) ->
               Σ[ r ∈ ℚ ] (r < q × U r)
      handle (r1 , r1<q , aU-r1) (r2 , r2<q , bU-r2) =
        max r1 r2 , (max-least-< r1<q r2<q ,
                     (isUpperSet≤ a max-≤-left aU-r1 ,
                      isUpperSet≤ b max-≤-right bU-r2))

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' q -> ∃[ r ∈ ℚ ] (q < r × L r)
      handle (inj-l aL-q) =
        ∥-map (\ (r , q<r , aL-r) -> r , q<r , ∣ inj-l aL-r ∣) (a.isUpperOpen-L q aL-q)
      handle (inj-r bL-q) =
        ∥-map (\ (r , q<r , bL-r) -> r , q<r , ∣ inj-r bL-r ∣) (b.isUpperOpen-L q bL-q)

    located : (x y : Rational) -> x < y -> ∥ L x ⊎ U y ∥
    located x y x<y = ∥-map2 handle (a.located x y x<y) (b.located x y x<y)
      where
      handle : (a.L x ⊎ a.U y) -> (b.L x ⊎ b.U y) -> (L x ⊎ U y)
      handle (inj-l aU) _          = inj-l ∣ inj-l aU ∣
      handle (inj-r aL) (inj-l bU) = inj-l ∣ inj-r bU ∣
      handle (inj-r aL) (inj-r bL) = inj-r (aL , bL)

    disjoint : Universal (Comp (L ∩ U))
    disjoint q (l , (aU , bU)) = unsquash isPropBot (∥-map handle l)
      where
      handle : a.L q ⊎ b.L q -> Bot
      handle (inj-l aL) = a.disjoint q (aL , aU)
      handle (inj-r bL) = b.disjoint q (bL , bU)

  abstract
    maxℝ : ℝ
    maxℝ = record
      { L = L
      ; U = U
      ; isProp-L = \_ -> squash
      ; isProp-U = \q -> isProp× (a.isProp-U q) (b.isProp-U q)
      ; Inhabited-L = Inhabited-L
      ; Inhabited-U = Inhabited-U
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; located = located
      ; disjoint = disjoint
      }


abstract
  maxℝ-≤-left : (x y : ℝ) -> x ≤ maxℝ x y
  maxℝ-≤-left x y xy<x = unsquash isPropBot (∥-map handle xy<x)
    where
    handle : ¬ (maxℝ x y ℝ<' x)
    handle (ℝ<'-cons q (xU-q , _) xL-q) = Real.disjoint x q (xL-q , xU-q)

  maxℝ-≤-right : (x y : ℝ) -> y ≤ maxℝ x y
  maxℝ-≤-right x y xy<y = unsquash isPropBot (∥-map handle xy<y)
    where
    handle : ¬ (maxℝ x y ℝ<' y)
    handle (ℝ<'-cons q (_ , yU-q) yL-q) = Real.disjoint y q (yL-q , yU-q)

  maxℝ-<-both : {z x y : ℝ} -> x < z -> y < z -> maxℝ x y < z
  maxℝ-<-both {z} {x} {y} x<z y<z = ∥-bind2 handle x<z y<z
    where
    handle : (x ℝ<' z) -> (y ℝ<' z) -> (maxℝ x y < z)
    handle (ℝ<'-cons q1 xU-q1 zL-q1) (ℝ<'-cons q2 yU-q2 zL-q2) =
      ∥-map handle2 (connex-≤ q1 q2)
      where
      handle2 : (q1 ≤ q2) ⊎ (q2 ≤ q1) -> maxℝ x y ℝ<' z
      handle2 (inj-l q1≤q2) = ℝ<'-cons q2 (isUpperSet≤ x q1≤q2 xU-q1 , yU-q2) zL-q2
      handle2 (inj-r q2≤q1) = ℝ<'-cons q1 (xU-q1 , isUpperSet≤ y q2≤q1 yU-q2) zL-q1
