{-# OPTIONS --cubical --safe --exact-split #-}

module real.rational where

open import additive-group
open import apartness
open import base
open import equality
open import hlevel
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-integral-domain
open import ordered-ring
open import ordered-semiring
open import rational
open import rational.integral-domain
open import rational.order
open import real
open import real.order
open import relation hiding (U)
open import truncation


abstract
  ℚ->ℝ : ℚ -> ℝ
  ℚ->ℝ q1 = record
    { L = L
    ; U = U
    ; isProp-L = \q2 -> isProp-<
    ; isProp-U = \q2 -> isProp-<
    ; Inhabited-L = Inhabited-L
    ; Inhabited-U = Inhabited-U
    ; isLowerSet-L = \q2<q3 q3<q1 -> trans-< q2<q3 q3<q1
    ; isUpperSet-U = \q2<q3 q1<q2 -> trans-< q1<q2 q2<q3
    ; isUpperOpen-L = isUpperOpen-L
    ; isLowerOpen-U = isLowerOpen-U
    ; disjoint = \q2 (l , u) -> asym-< {_} {_} {_} {q2} {q1} l u
    ; located = located
    }
    where
    module _ where
      L : Pred ℚ ℓ-zero
      L = \q2 -> q2 < q1
      U : Pred ℚ ℓ-zero
      U = \q2 -> q1 < q2
      Inhabited-L : Inhabited L
      Inhabited-L = ∣ q1 r+ (r- 1r)  , lt2 ∣
        where
        lt1 : (q1 r+ (r- 1r)) < (q1 r+ 0r)
        lt1 = +₁-preserves-< (minus-flips-0< (Pos-0< 1r Pos-1r))
        lt2 : (q1 r+ (r- 1r)) < q1
        lt2 = subst ((q1 r+ (r- 1r)) <_) (r+-right-zero q1) lt1

      Inhabited-U : Inhabited U
      Inhabited-U = ∣ q1 r+ 1r  , lt2 ∣
        where
        lt1 : (q1 r+ 1r) > (q1 r+ 0r)
        lt1 = +₁-preserves-< (Pos-0< 1r Pos-1r)
        lt2 : (q1 r+ 1r) > q1
        lt2 = subst ((q1 r+ 1r) >_) (r+-right-zero q1) lt1

      located : (q2 q3 : Rational) -> q2 < q3 -> ∥ q2 < q1 ⊎ q1 < q3 ∥
      located q2 q3 lt = ∥-map handle (dense-< {q2} {q3} lt)
        where
        handle : Σ[ z ∈ ℚ ] (q2 < z × z < q3) -> q2 < q1 ⊎ q1 < q3
        handle (z , q2<z , z<q3) = handle2 (decide-< q1 z) (decide-< z q1)
          where
          handle2 : Dec (q1 < z) -> Dec (z < q1) -> q2 < q1 ⊎ q1 < q3
          handle2 (yes lt) _        = inj-r (trans-< {_} {_} {_} {q1} {z} {q3} lt z<q3)
          handle2 (no _)   (yes lt) = inj-l (trans-< {_} {_} {_} {q2} {z} {q1} q2<z lt)
          handle2 (no q1≮z) (no z≮q1) =
            inj-l (subst (q2 <_) (connected-< {_} {_} {_} {z} {q1} z≮q1 q1≮z) q2<z)

      isUpperOpen-L : (q2 : ℚ) -> L q2 -> ∃[ q3 ∈ ℚ ] (q2 < q3 × L q3)
      isUpperOpen-L q2 q2<q1 = dense-< {q2} {q1} q2<q1

      isLowerOpen-U : (q2 : ℚ) -> U q2 -> ∃[ q3 ∈ ℚ ] (q3 < q2 × U q3)
      isLowerOpen-U q2 q1<q2 =
        ∥-map (\ (q3 , q1<q3 , q3<q2) -> q3 , q3<q2 , q1<q3) (dense-< {q1} {q2} q1<q2)

abstract
  ℚ->ℝ-preserves-< : (q1 q2 : ℚ) -> (q1 < q2) -> (ℚ->ℝ q1) ℝ< (ℚ->ℝ q2)
  ℚ->ℝ-preserves-< q1 q2 lt = ∥-map handle (dense-< {q1} {q2} lt)
    where
    handle : Σ[ q ∈ ℚ ] (q1 < q × q < q2) -> (ℚ->ℝ q1) ℝ<' (ℚ->ℝ q2)
    handle (q , l , u) = ℝ<'-cons q l u

  ℚ->ℝ-preserves-≤ : (q1 q2 : ℚ) -> (q1 ≤ q2) -> (ℚ->ℝ q1) ≤ (ℚ->ℝ q2)
  ℚ->ℝ-preserves-≤ q1 q2 q1≤q2 q2<q1 = unsquash isPropBot (∥-map handle q2<q1)
    where
    handle : (ℚ->ℝ q2) ℝ<' (ℚ->ℝ q1) -> Bot
    handle (ℝ<'-cons q q2<q q<q1) = irrefl-< (trans-< q<q1 (trans-≤-< q1≤q2 q2<q))

  ℚ<->L : {q r : ℚ} -> q < r -> Real.L (ℚ->ℝ r) q
  ℚ<->L q<r = q<r

  ℚ<->U : {q r : ℚ} -> q < r -> Real.U (ℚ->ℝ q) r
  ℚ<->U q<r = q<r

  L->ℚ< : {q r : ℚ} -> Real.L (ℚ->ℝ r) q -> q < r
  L->ℚ< q<r = q<r

  U->ℚ< : {q r : ℚ} -> Real.U (ℚ->ℝ q) r -> q < r
  U->ℚ< q<r = q<r

  ℝ<->U : {x : ℝ} {q : ℚ} -> x ℝ< (ℚ->ℝ q) -> Real.U x q
  ℝ<->U {x} {q} x<q = unsquash (x.isProp-U q) (∥-map handle x<q)
    where
    module x = Real x
    handle : x ℝ<' (ℚ->ℝ q) -> Real.U x q
    handle (ℝ<'-cons r xu-r r<q) = x.isUpperSet-U r<q xu-r

  ℝ<->L : {q : ℚ} {x : ℝ} -> (ℚ->ℝ q) ℝ< x -> Real.L x q
  ℝ<->L {q} {x} q<x = unsquash (x.isProp-L q) (∥-map handle q<x)
    where
    module x = Real x
    handle : (ℚ->ℝ q) ℝ<' x -> Real.L x q
    handle (ℝ<'-cons r q<r xl-r) = x.isLowerSet-L q<r xl-r

  L->ℝ< : {x : ℝ} {q : ℚ} -> Real.L x q -> (ℚ->ℝ q) ℝ< x
  L->ℝ< {x} {q} q<x = ∥-bind handle (Real.isUpperOpen-L x _ q<x)
    where
    handle : Σ[ r ∈ ℚ ] (q < r × Real.L x r) -> (ℚ->ℝ q) ℝ< x
    handle (r , q<r , r<x) = ∣ ℝ<'-cons r q<r r<x ∣

  U->ℝ< : {x : ℝ} {q : ℚ} -> Real.U x q -> x ℝ< (ℚ->ℝ q)
  U->ℝ< {x} {q} x<q = ∥-bind handle (Real.isLowerOpen-U x _ x<q)
    where
    handle : Σ[ r ∈ ℚ ] (r < q × Real.U x r) -> x ℝ< (ℚ->ℝ q)
    handle (r , r<q , x<r) = ∣ ℝ<'-cons r x<r r<q ∣

-- Constants

0ℝ : ℝ
0ℝ = ℚ->ℝ 0r

1ℝ : ℝ
1ℝ = ℚ->ℝ 1r

0ℝ<1ℝ : 0ℝ ℝ< 1ℝ
0ℝ<1ℝ = ℚ->ℝ-preserves-< 0r 1r 0<1

-- Properties with the constants

abstract
  ℝ≮0-¬U0 : (x : ℝ) -> ¬ (x ℝ< 0ℝ) -> ¬ (Real.U x 0r)
  ℝ≮0-¬U0 x x≮0 xU-0r = unsquash isPropBot (∥-map handle (x.isLowerOpen-U 0r xU-0r))
    where
    module x = Real x
    handle : ¬ (Σ[ r ∈ ℚ ] (r < 0# × x.U r))
    handle (r , r<0 , xU-r) = x≮0 (∣ ℝ<'-cons r xU-r r<0 ∣)

  ℝ≮0-L∀<0 : (x : ℝ) -> ¬ (x ℝ< 0ℝ) -> {q : ℚ} -> q < 0r -> Real.L x q
  ℝ≮0-L∀<0 x x≮0 {q} q<0 = unsquash (x.isProp-L q) (∥-map handle (x.located q 0r q<0))
    where
    module x = Real x
    handle : x.L q ⊎ x.U 0r -> x.L q
    handle (inj-l l) = l
    handle (inj-r u) = bot-elim (ℝ≮0-¬U0 x x≮0 u)

ℝInv : Pred ℝ ℓ-one
ℝInv x = x # 0ℝ

isProp-ℝInv : (x : ℝ) -> isProp (ℝInv x)
isProp-ℝInv x = isProp-#
