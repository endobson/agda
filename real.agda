{-# OPTIONS --cubical --safe --exact-split #-}

module real where

open import base
open import equality
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
  isLowerOpen U = (x : Rational) -> U x -> Σ[ y ∈ Rational ] (y < x × U y)

  isUpperOpen : Pred Rational ℓ -> Type ℓ
  isUpperOpen L = (x : Rational) -> L x -> Σ[ y ∈ Rational ] (x < y × L y)

record Real (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : Pred Rational ℓ
    U : Pred Rational ℓ
    isProp-L : isPropValuedPred L
    isProp-U : isPropValuedPred U
    isLowerSet-L : isLowerSet L
    isUpperSet-U : isUpperSet U
    disjoint : Universal (Comp (L ∩ U))
    located : (x y : Rational) -> x < y -> ∥ L x ⊎ U y ∥

ℝ = Real ℓ-zero

ℚ->ℝ : ℚ -> ℝ
ℚ->ℝ q1 = record
  { L = \q2 -> q2 < q1
  ; U = \q2 -> q1 < q2
  ; isProp-L = \q2 -> isProp-< {q2} {q1}
  ; isProp-U = \q2 -> isProp-< {q1} {q2}
  ; isLowerSet-L = \q2 q3 q2<q3 q3<q1 -> trans-< {q2} {q3} {q1} q2<q3 q3<q1
  ; isUpperSet-U = \q2 q3 q2<q3 q1<q2 -> trans-< {q1} {q2} {q3} q1<q2 q2<q3
  ; disjoint = \q2 (l , u) -> asym-< {q2} {q1} l u
  ; located = located
  }
  where
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



--sqrtℚ : ℚ -> ℝ
--sqrtℚ q1 = record
--  { L = \q2 -> (q2 r* q2) < q1
--  ; U = \q2 -> q1 < (q2 r* q2)
--  ; isLowerSet-L = \q2 q3 q2<q3 q3<q1 -> trans-< {q2} {q3} {q1} q2<q3 q3<q1
--  ; isUpperSet-U = \q2 q3 q2<q3 q1<q2 -> trans-< {q1} {q2} {q3} q1<q2 q2<q3
--  }
