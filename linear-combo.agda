{-# OPTIONS --cubical --safe --exact-split #-}

module linear-combo where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import commutative-monoid
open import equality
open import functions
open import int
open import nat
open import ring
open import ring.implementations.int
open import semiring

open EqReasoning

record LinearCombination (a : Int) (b : Int) (d : Int) : Set where
  constructor linear-combo
  field
    x : Int
    y : Int
    path : x * a + y * b == d

LinearCombination' : Nat -> Nat -> Nat -> Set
LinearCombination' a b d = LinearCombination (int a) (int b) (int d)


linear-combo-refl : {n : Int}  -> LinearCombination n n n
linear-combo-refl {n} =
  (linear-combo zero-int (pos zero) (+-left *-left-zero >=> +-left-zero >=> *-left-one))

linear-combo-sym : {a b d : Int} -> LinearCombination a b d -> LinearCombination b a d
linear-combo-sym {a} {b} {d} (linear-combo x y p) =
  (linear-combo y x (+-commute >=> p))

linear-combo-zero : {n : Int}  -> LinearCombination n zero-int n
linear-combo-zero {n} =
  (linear-combo-sym
    (linear-combo zero-int (pos zero)
                  (+-left *-left-zero >=> +-left-zero >=> *-left-one)))

linear-combo-negate : {a b d : Int} -> LinearCombination a b d -> LinearCombination a (- b) d
linear-combo-negate {a} {b} {d} (linear-combo x y p) =
  (linear-combo x (- y) proof)
  where
    proof : x * a + (- y * - b) == d
    proof =
      begin
        x * a + (- y * - b)
      ==< +-right minus-extract-both >
        x * a + y * b
      ==< p >
        d
      end


linear-combo-negate-result : {a b d : Int} -> LinearCombination a b d -> LinearCombination a b (- d)
linear-combo-negate-result {a} {b} {d} (linear-combo x y p) =
  (linear-combo (- x) (- y) proof)
  where
    proof : (- x * a) + (- y * b) == - d
    proof =
      begin
        - x * a + - y * b
      ==< +-left minus-extract-left >
        - (x * a) + - y * b
      ==< +-right minus-extract-left >
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

module _ where
  private
    lc-na : {a b d : Int} -> LinearCombination a b d -> LinearCombination (- a) b d
    lc-na = linear-combo-sym ∘ linear-combo-negate ∘ linear-combo-sym
    lc-nb = linear-combo-negate
    lc-nd = linear-combo-negate-result

  linear-combo-unabs : (a b d : Int)
                       -> LinearCombination (abs a) (abs b) (abs d)
                       -> LinearCombination a b d
  linear-combo-unabs (nonneg a) (nonneg b) (nonneg d) l = l
  linear-combo-unabs (nonneg a) (nonneg b) (neg d)    l = (lc-nd l)
  linear-combo-unabs (nonneg a) (neg b)    (nonneg d) l = (lc-nb l)
  linear-combo-unabs (nonneg a) (neg b)    (neg d)    l = (lc-nb (lc-nd l))
  linear-combo-unabs (neg a)    (nonneg b) (nonneg d) l = (lc-na l)
  linear-combo-unabs (neg a)    (nonneg b) (neg d)    l = (lc-na (lc-nd l))
  linear-combo-unabs (neg a)    (neg b)    (nonneg d) l = (lc-na (lc-nb l))
  linear-combo-unabs (neg a)    (neg b)    (neg d)    l = (lc-na (lc-nb (lc-nd l)))

linear-combo-+' : {a b d : Nat}
                  -> LinearCombination' a b d
                  -> LinearCombination' a (a +' b) d
linear-combo-+' {a} {b} {d} (linear-combo x y p) =
    (linear-combo (x + (- y)) y path)
    where
    path : (x + (- y)) * (int a) + y * (int (a +' b)) == (int d)
    path =
      begin
        (x + (- y)) * (int a) + y * (int (a +' b))
      ==< +-left *-distrib-+-right >
        ((x * (int a)) + ((- y) * (int a))) + y * (int (a +' b))
      ==< (\i  -> ((x * (int a)) + ((- y) * (int a))) + y * (CommMonoidʰ.preserves-∙ int-+ʰ a b i)) >
        ((x * (int a)) + ((- y) * (int a))) + y * ((int a) + (int b))
      ==< cong (\c -> ((x * (int a)) + ((- y) * (int a))) + c) *-distrib-+-left >
        ((x * (int a)) + ((- y) * (int a))) + ((y * (int a)) + (y * (int b)))
      ==< +-assoc >
        (x * (int a)) + (((- y) * (int a)) + ((y * (int a)) + (y * (int b))))
      ==< +-right (sym +-assoc) >
        (x * (int a)) + ((((- y) * (int a)) + (y * (int a))) + (y * (int b)))
      ==< +-right (+-left (sym (*-distrib-+-right))) >
        (x * (int a)) + ((((- y) + y) * (int a)) + (y * (int b)))
      ==< +-right (+-left (*-left (+-commute >=> add-minus-zero) >=> *-left-zero)) >
        x * (int a) + (int 0 + y * (int b))
      ==< +-right +-left-zero >
        x * (int a) + y * (int b)
      ==< p >
        (int d)
      end
