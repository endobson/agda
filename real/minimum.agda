{-# OPTIONS --cubical --safe --exact-split #-}

module real.minimum where

open import real
open import base
open import hlevel
open import truncation
open import relation hiding (U)
open import rational
open import rational.order
open import real.interval
open import real.rational
open import real.order
open import order
open import order.instances.real
open import sum
open import order.instances.rational

module _ (a b : ℝ) where
  private
    module a = Real a
    module b = Real b
    L : Pred ℚ ℓ-zero
    L q = a.L q × b.L q

    U' : Pred ℚ ℓ-zero
    U' q = a.U q ⊎ b.U q

    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥

    Inhabited-L : ∃ ℚ L
    Inhabited-L = ∥-bind2 handle a.Inhabited-L b.Inhabited-L
      where
      handle : Σ ℚ a.L -> Σ ℚ b.L -> ∃ ℚ L
      handle (q1 , aL-q1) (q2 , bL-q2) = ∥-map handle2 (connex-≤ q1 q2)
        where
        handle2 : (q1 ≤ q2) ⊎ (q2 ≤ q1) -> Σ ℚ L
        handle2 (inj-l q1≤q2) = q1 , (aL-q1 , isLowerSet≤ b q1≤q2 bL-q2)
        handle2 (inj-r q2≤q1) = q2 , (isLowerSet≤ a q2≤q1 aL-q1 , bL-q2)

    isLowerSet-L : isLowerSet L
    isLowerSet-L q<r (aL-r , bL-r) =
      (a.isLowerSet-L q<r aL-r , b.isLowerSet-L q<r bL-r)

    isUpperSet-U : isUpperSet U
    isUpperSet-U {q} {r} q<r = ∥-map handle
      where
      handle : U' q -> U' r
      handle (inj-l aU-q) = inj-l (a.isUpperSet-U q<r aU-q)
      handle (inj-r bU-q) = inj-r (b.isUpperSet-U q<r bU-q)

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q (aL-q , bL-q) =
      ∥-bind2 handle (a.isUpperOpen-L q aL-q) (b.isUpperOpen-L q bL-q)
      where
      handle : Σ[ r1 ∈ ℚ ] (q < r1 × a.L r1) -> Σ[ r2 ∈ ℚ ] (q < r2 × b.L r2) ->
               ∃[ r ∈ ℚ ] (q < r × L r)
      handle (r1 , q<r1 , aL-r1) (r2 , q<r2 , bL-r2) = ∥-map handle2 (connex-≤ r1 r2)
        where
        handle2 : (r1 ≤ r2) ⊎ (r2 ≤ r1) -> Σ[ r ∈ ℚ ] (q < r × L r)
        handle2 (inj-l r1≤r2) = r1 , q<r1 , aL-r1 , isLowerSet≤ b r1≤r2 bL-r2
        handle2 (inj-r r2≤r1) = r2 , q<r2 , isLowerSet≤ a r2≤r1 aL-r1 , bL-r2


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-bind handle
      where
      handle : U' q -> ∃[ r ∈ ℚ ] (r < q × U r)
      handle (inj-l aU-q) =
        ∥-map (\ (r , r<q , aU-r) -> r , r<q , ∣ inj-l aU-r ∣) (a.isLowerOpen-U q aU-q)
      handle (inj-r bU-q) =
        ∥-map (\ (r , r<q , bU-r) -> r , r<q , ∣ inj-r bU-r ∣) (b.isLowerOpen-U q bU-q)

    located : (x y : Rational) -> x < y -> ∥ L x ⊎ U y ∥
    located x y x<y = ∥-map2 handle (a.located x y x<y) (b.located x y x<y)
      where
      handle : (a.L x ⊎ a.U y) -> (b.L x ⊎ b.U y) -> (L x ⊎ U y)
      handle (inj-l aL) (inj-l bL) = inj-l (aL , bL)
      handle (inj-l aL) (inj-r bU) = inj-r ∣ inj-r bU ∣
      handle (inj-r aU) _          = inj-r ∣ inj-l aU ∣


    disjoint : Universal (Comp (L ∩ U))
    disjoint q ((aL , bL) , u) = unsquash isPropBot (∥-map handle u)
      where
      handle : a.U q ⊎ b.U q -> Bot
      handle (inj-l aU) = a.disjoint q (aL , aU)
      handle (inj-r bU) = b.disjoint q (bL , bU)

  abstract
    minℝ : ℝ
    minℝ = record
      { L = L
      ; U = U
      ; isProp-L = \q -> isProp× (a.isProp-L q) (b.isProp-L q)
      ; isProp-U = \_ -> squash
      ; Inhabited-L = Inhabited-L
      ; Inhabited-U = ∥-map (\(q , u) -> q , ∣ inj-l u ∣) a.Inhabited-U
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; located = located
      ; disjoint = disjoint
      }

abstract
  minℝ-≤-left : (x y : ℝ) -> minℝ x y ≤ x
  minℝ-≤-left x y x<xy = unsquash isPropBot (∥-map handle x<xy)
    where
    handle : ¬ (x ℝ<' minℝ x y)
    handle (ℝ<'-cons q xU-q (xL-q , _)) = Real.disjoint x q (xL-q , xU-q)

  minℝ-≤-right : (x y : ℝ) -> minℝ x y ≤ y
  minℝ-≤-right x y x<xy = unsquash isPropBot (∥-map handle x<xy)
    where
    handle : ¬ (y ℝ<' minℝ x y)
    handle (ℝ<'-cons q yU-q (_ , yL-q)) = Real.disjoint y q (yL-q , yU-q)

  minℝ-<-both : {z x y : ℝ} -> z < x -> z < y -> z < minℝ x y
  minℝ-<-both {z} {x} {y} z<x z<y = ∥-bind2 handle z<x z<y
    where
    handle : (z ℝ<' x) -> (z ℝ<' y) -> (z < minℝ x y)
    handle (ℝ<'-cons q1 zU-q1 xL-q1) (ℝ<'-cons q2 zU-q2 yL-q2) =
      ∥-map handle2 (connex-≤ q1 q2)
      where
      handle2 : (q1 ≤ q2) ⊎ (q2 ≤ q1) -> z ℝ<' minℝ x y
      handle2 (inj-l q1≤q2) = ℝ<'-cons q1 zU-q1 (xL-q1 , isLowerSet≤ y q1≤q2 yL-q2)
      handle2 (inj-r q2≤q1) = ℝ<'-cons q2 zU-q2 (isLowerSet≤ x q2≤q1 xL-q1 , yL-q2)
