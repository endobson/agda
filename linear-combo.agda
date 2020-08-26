{-# OPTIONS --cubical --safe --exact-split #-}

module linear-combo where

open import abs
open import base
open import equality
open import int
open import nat
open import commutative-monoid
open import ring.implementations


data LinearCombination : Int -> Int -> Int -> Set where
 linear-combo : (a : Int) -> (b : Int) -> (d : Int) -> (x : Int) -> (y : Int)
   -> {x * a + y * b == d}
   -> LinearCombination a b d

LinearCombination' : Nat -> Nat -> Nat -> Set
LinearCombination' a b d = LinearCombination (int a) (int b) (int d)


linear-combo-refl : {n : Int}  -> LinearCombination n n n
linear-combo-refl {n} = (linear-combo n n n zero-int (pos zero) {+-right-zero {n}})

linear-combo-sym : {a b d : Int} -> LinearCombination a b d -> LinearCombination b a d
linear-combo-sym (linear-combo a b d x y {p}) =
  (linear-combo b a d y x {+-commute {y * b} >=> p})

linear-combo-zero : {n : Int}  -> LinearCombination n zero-int n
linear-combo-zero {n} =
  (linear-combo-sym (linear-combo zero-int n n zero-int (pos zero) {+-right-zero {n}}))

linear-combo-negate : {a b d : Int} -> LinearCombination a b d -> LinearCombination a (- b) d
linear-combo-negate (linear-combo a b d x y {p}) =
  (linear-combo a (- b) d x (- y) {proof})
  where
    proof : x * a + (- y * - b) == d
    proof =
      begin
        x * a + (- y * - b)
      ==< +-right {x * a} (minus-extract-both {y} {b}) >
        x * a + y * b
      ==< p >
        d
      end


linear-combo-negate-result : {a b d : Int} -> LinearCombination a b d -> LinearCombination a b (- d)
linear-combo-negate-result (linear-combo a b d x y {p}) =
  (linear-combo a b (- d) (- x) (- y) {proof})
  where
    proof : (- x * a) + (- y * b) == - d
    proof =
      begin
        - x * a + - y * b
      ==< +-left (minus-extract-left {x}) >
        - (x * a) + - y * b
      ==< +-right { - (x * a)} (minus-extract-left {y}) >
        - (x * a) + - (y * b)
      ==< sym (minus-distrib-+ {x * a}) >
        - ((x * a) + (y * b))
      ==< cong minus p >
        - d
      end

linear-combo-abs : {a b d : Int} -> LinearCombination a b d -> LinearCombination a b (abs d)
linear-combo-abs {a} {b} {zero-int} lc = lc
linear-combo-abs {a} {b} {pos _} lc = lc
linear-combo-abs {a} {b} {neg _} lc = (linear-combo-negate-result lc)

linear-combo-+' : {a b d : Nat}
                  -> LinearCombination' a b d
                  -> LinearCombination' a (a +' b) d
linear-combo-+' {a} {b} {d} (linear-combo _ _ _ x y {p}) =
    (linear-combo (int a) (int (a +' b)) (int d) (x + (- y)) y {path})
    where
    path : (x + (- y)) * (int a) + y * (int (a +' b)) == (int d)
    path =
      begin
        (x + (- y)) * (int a) + y * (int (a +' b))
      ==< +-left (*-distrib-+ {x} {(- y)} {int a}) >
        ((x * (int a)) + ((- y) * (int a))) + y * (int (a +' b))
      ==< (\i  -> ((x * (int a)) + ((- y) * (int a))) + y * (CommMonoidʰ.preserves-∙ int-+ʰ a b i)) >
        ((x * (int a)) + ((- y) * (int a))) + y * ((int a) + (int b))
      ==< (\i  -> ((x * (int a)) + ((- y) * (int a))) + (*-distrib-+-left {y} {int a} {int b} i)) >
        ((x * (int a)) + ((- y) * (int a))) + ((y * (int a)) + (y * (int b)))
      ==< +-assoc {x * (int a)} {(- y) * (int a)} >
        (x * (int a)) + (((- y) * (int a)) + ((y * (int a)) + (y * (int b))))
      ==< +-right {x * (int a)} (sym (+-assoc {(- y) * (int a)} {y * (int a)})) >
        (x * (int a)) + ((((- y) * (int a)) + (y * (int a))) + (y * (int b)))
      ==< +-right {x * (int a)} (+-left (sym (*-distrib-+ {(- y)} {y} {int a}))) >
        (x * (int a)) + ((((- y) + y) * (int a)) + (y * (int b)))
      ==< +-right {x * (int a)} (+-left (*-left (+-commute {(- y)} {y} >=> add-minus-zero {y}))) >
        x * (int a) + y * (int b)
      ==< p >
        (int d)
      end
