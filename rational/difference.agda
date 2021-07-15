{-# OPTIONS --cubical --safe --exact-split #-}

module rational.difference where

open import base
open import equality
open import ring.implementations.rational
open import rational
open import semiring

diffℚ : ℚ -> ℚ -> ℚ
diffℚ x y = (y r+ (r- x))

abstract
  diffℚ-anticommute : (x y : ℚ) -> diffℚ x y == r- (diffℚ y x)
  diffℚ-anticommute x y = sym (
    RationalRing.minus-distrib-plus {x} {r- y} >=>
    cong ((r- x) r+_) (RationalRing.minus-double-inverse {y}) >=>
    r+-commute (r- x) y)

  r+-swap-diffℚ : (a b c d : Rational) -> ((diffℚ a b) r+ (diffℚ c d)) == (diffℚ (a r+ c) (b r+ d))
  r+-swap-diffℚ a b c d =
    r+-assoc b (r- a) (diffℚ c d) >=>
    cong (b r+_) (sym (r+-assoc (r- a) d (r- c)) >=>
                  cong (_r+ (r- c)) (r+-commute (r- a) d) >=>
                  r+-assoc d (r- a) (r- c) >=>
                  cong (d r+_) (sym (RationalRing.minus-distrib-plus {a} {c}))) >=>
    sym (r+-assoc b d (r- (a r+ c)))

  r*-distrib-diffℚ : (a b c : Rational) -> a r* (diffℚ b c) == diffℚ (a r* b) (a r* c)
  r*-distrib-diffℚ a b c =
    RationalSemiring.*-distrib-+-left {a} {c} {r- b} >=>
    cong ((a r* c) r+_) (r*-minus-extract-right a b)


  diffℚ-trans : (x y z : ℚ) -> diffℚ x y r+ diffℚ y z == (diffℚ x z)
  diffℚ-trans x y z =
    r+-commute (diffℚ x y) (diffℚ y z) >=>
    r+-assoc z (r- y) (diffℚ x y) >=>
    cong (z r+_) (sym (r+-assoc (r- y) y (r- x)) >=>
                  cong (_r+ (r- x)) (r+-commute (r- y) y >=> r+-inverse y) >=>
                  r+-left-zero (r- x))

  diffℚ-step : (x y : ℚ) -> x + diffℚ x y == y
  diffℚ-step x y =
    sym (r+-assoc x y (r- x)) >=>
    cong (_r+ (r- x)) (r+-commute x y) >=>
    (r+-assoc y x (r- x)) >=>
    cong (y r+_) (r+-inverse x) >=>
    r+-right-zero y
