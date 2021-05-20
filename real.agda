{-# OPTIONS --cubical --safe --exact-split #-}

module real where

open import base
open import rational
open import rational.order
open import relation hiding (U)

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
    isLowerSet-L : isLowerSet L
    isUpperSet-U : isUpperSet U

ℝ = Real ℓ-zero

ℚ->ℝ : ℚ -> ℝ
ℚ->ℝ q1 = record
  { L = \q2 -> q2 < q1
  ; U = \q2 -> q1 < q2
  ; isLowerSet-L = \q2 q3 q2<q3 q3<q1 -> trans-< {q2} {q3} {q1} q2<q3 q3<q1
  ; isUpperSet-U = \q2 q3 q2<q3 q1<q2 -> trans-< {q1} {q2} {q3} q1<q2 q2<q3
  }

--sqrtℚ : ℚ -> ℝ
--sqrtℚ q1 = record
--  { L = \q2 -> (q2 r* q2) < q1
--  ; U = \q2 -> q1 < (q2 r* q2)
--  ; isLowerSet-L = \q2 q3 q2<q3 q3<q1 -> trans-< {q2} {q3} {q1} q2<q3 q3<q1
--  ; isUpperSet-U = \q2 q3 q2<q3 q1<q2 -> trans-< {q1} {q2} {q3} q1<q2 q2<q3
--  }
