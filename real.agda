{-# OPTIONS --cubical --safe --exact-split #-}

module real where

open import base
open import equality
open import hlevel
open import rational
open import rational.order
open import relation hiding (U)
open import truncation

private
  variable
    ℓ : Level


private
  isLowerSet : Pred Rational ℓ -> Type ℓ
  isLowerSet L = (x y : Rational) -> x < y -> L y -> L x

  isUpperSet : Pred Rational ℓ -> Type ℓ
  isUpperSet U = (x y : Rational) -> x < y -> U x -> U y

  isLowerOpen : Pred Rational ℓ -> Type ℓ
  isLowerOpen U = (x : Rational) -> U x -> ∃[ y ∈ Rational ] (y < x × U y)

  isUpperOpen : Pred Rational ℓ -> Type ℓ
  isUpperOpen L = (x : Rational) -> L x -> ∃[ y ∈ Rational ] (x < y × L y)

record Real (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : Pred Rational ℓ
    U : Pred Rational ℓ
    isProp-L : isPropValuedPred L
    isProp-U : isPropValuedPred U
    Inhabited-L : Inhabited L
    Inhabited-U : Inhabited U
    isLowerSet-L : isLowerSet L
    isUpperSet-U : isUpperSet U
    isUpperOpen-L : isUpperOpen L
    isLowerOpen-U : isLowerOpen U
    disjoint : Universal (Comp (L ∩ U))
    located : (x y : Rational) -> x < y -> ∥ L x ⊎ U y ∥

ℝ = Real ℓ-zero

ℚ->ℝ : ℚ -> ℝ
ℚ->ℝ q1 = record
  { L = L
  ; U = U
  ; isProp-L = \q2 -> isProp-< {q2} {q1}
  ; isProp-U = \q2 -> isProp-< {q1} {q2}
  ; Inhabited-L = Inhabited-L
  ; Inhabited-U = Inhabited-U
  ; isLowerSet-L = \q2 q3 q2<q3 q3<q1 -> trans-< {q2} {q3} {q1} q2<q3 q3<q1
  ; isUpperSet-U = \q2 q3 q2<q3 q1<q2 -> trans-< {q1} {q2} {q3} q1<q2 q2<q3
  ; isUpperOpen-L = isUpperOpen-L
  ; isLowerOpen-U = isLowerOpen-U
  ; disjoint = \q2 (l , u) -> asym-< {q2} {q1} l u
  ; located = located
  }
  where
  L = \q2 -> q2 < q1
  U = \q2 -> q1 < q2
  Inhabited-L : Inhabited L
  Inhabited-L = ∣ q1 r+ (r- 1r)  , lt2 ∣
    where
    lt1 : (q1 r+ (r- 1r)) < (q1 r+ 0r)
    lt1 = r+₁-preserves-order q1 (r- 1r) 0r (r--flips-order 0r 1r (Pos-0< 1r Pos-1r))
    lt2 : (q1 r+ (r- 1r)) < q1
    lt2 = subst ((q1 r+ (r- 1r)) <_) (r+-right-zero q1) lt1

  Inhabited-U : Inhabited U
  Inhabited-U = ∣ q1 r+ 1r  , lt2 ∣
    where
    lt1 : (q1 r+ 1r) > (q1 r+ 0r)
    lt1 = r+₁-preserves-order q1 0r 1r (Pos-0< 1r Pos-1r)
    lt2 : (q1 r+ 1r) > q1
    lt2 = subst ((q1 r+ 1r) >_) (r+-right-zero q1) lt1

  located : (q2 q3 : Rational) -> q2 < q3 -> ∥ q2 < q1 ⊎ q1 < q3 ∥
  located q2 q3 lt = handle (decide-< q1 z) (decide-< z q1)
    where
    Σz = (dense-< {q2} {q3} lt)
    z = fst Σz
    q2<z = proj₁ (snd Σz)
    z<q3 = proj₂ (snd Σz)
    handle : Dec (q1 < z) -> Dec (z < q1) -> ∥ q2 < q1 ⊎ q1 < q3 ∥
    handle (yes lt) _        = ∣ inj-r (trans-< {q1} {z} {q3} lt z<q3) ∣
    handle (no _)   (yes lt) = ∣ inj-l (trans-< {q2} {z} {q1} q2<z lt) ∣
    handle (no q1≮z) (no z≮q1) = ∣ inj-l (subst (q2 <_) (connected-< {z} {q1} z≮q1 q1≮z) q2<z) ∣

  isUpperOpen-L : (q2 : ℚ) -> L q2 -> ∃[ q3 ∈ ℚ ] (q2 < q3 × L q3)
  isUpperOpen-L q2 q2<q1 = ∣ dense-< {q2} {q1} q2<q1 ∣

  isLowerOpen-U : (q2 : ℚ) -> U q2 -> ∃[ q3 ∈ ℚ ] (q3 < q2 × U q3)
  isLowerOpen-U q2 q1<q2 = ∣ fst d , (proj₂ (snd d) , proj₁ (snd d)) ∣
    where
    d = dense-< {q1} {q2} q1<q2

_ℝ<'_ : ℝ -> ℝ -> Type₀
x ℝ<' y = Σ[ q ∈ ℚ ] (Real.U x q × Real.L y q)

_ℝ<_ : ℝ -> ℝ -> Type₀
x ℝ< y = ∃[ q ∈ ℚ ] (Real.U x q × Real.L y q)

ℚ->ℝ-preserves-< : (q1 q2 : ℚ) -> (q1 < q2) -> (ℚ->ℝ q1) ℝ< (ℚ->ℝ q2)
ℚ->ℝ-preserves-< q1 q2 lt = ∣ dense-< {q1} {q2} lt ∣

isProp-ℝ< : (x y : ℝ) -> isProp (x ℝ< y)
isProp-ℝ< x y = squash

asym-ℝ< : Asymmetric _ℝ<_
asym-ℝ< {x} {y} x<y y<x = unsquash isPropBot (∥-map2 handle x<y y<x)
  where
  handle-same : (q1 q2 : Rational)
                -> (Real.U x q1 × Real.L y q1)
                -> (Real.U y q2 × Real.L x q2)
                -> q1 == q2 -> Bot
  handle-same q1 q2 (uq1 , _ ) (_ , lq2) p =
    Real.disjoint x q2 (lq2 , (subst (Real.U x) p uq1))


  handle-diff : (q1 q2 : Rational)
                (x y : ℝ)
                -> (Real.U x q1 × Real.L y q1)
                -> (Real.U y q2 × Real.L x q2)
                -> q1 < q2 -> Bot
  handle-diff q1 q2 x y (uq1 , _ ) (_ , lq2) lt =
    Real.disjoint x q2 (lq2 , Real.isUpperSet-U x q1 q2 lt uq1)

  handle-tri : (q1 q2 : Rational)
               -> (Real.U x q1 × Real.L y q1)
               -> (Real.U y q2 × Real.L x q2)
               -> Tri (q1 < q2) (q1 == q2) (q2 < q1)
               -> Bot
  handle-tri q1 q2 p1 p2 (tri< lt _ _)   = handle-diff q1 q2 x y p1 p2 lt
  handle-tri q1 q2 p1 p2 (tri= _ path _) = handle-same q1 q2 p1 p2 path
  handle-tri q1 q2 p1 p2 (tri> _ _ lt)   = handle-diff q2 q1 y x p2 p1 lt

  handle : x ℝ<' y -> y ℝ<' x -> Bot
  handle (q1 , p1) (q2 , p2) =
    handle-tri q1 q2 p1 p2 (trichotomous-< q1 q2)


_ℝ#_ : ℝ -> ℝ -> Type₀
x ℝ# y = (x ℝ< y) ⊎ (y ℝ< x)

isProp-ℝ# : (x y : ℝ) -> isProp (x ℝ# y)
isProp-ℝ# x y = isProp⊎ (isProp-ℝ< x y) (isProp-ℝ< y x) (asym-ℝ< {x} {y})


--sqrtℚ : ℚ -> ℝ
--sqrtℚ q1 = record
--  { L = \q2 -> (q2 r* q2) < q1
--  ; U = \q2 -> q1 < (q2 r* q2)
--  ; isLowerSet-L = \q2 q3 q2<q3 q3<q1 -> trans-< {q2} {q3} {q1} q2<q3 q3<q1
--  ; isUpperSet-U = \q2 q3 q2<q3 q1<q2 -> trans-< {q1} {q2} {q3} q1<q2 q2<q3
--  }
