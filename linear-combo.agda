{-# OPTIONS --cubical --safe --exact-split #-}

module linear-combo where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import commutative-monoid
open import equality
open import functions
open import int.base
open import nat
open import order
open import order.instances.int
open import order.minmax.instances.int
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.int
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
      ==< sym minus-distrib-plus >
        - ((x * a) + (y * b))
      ==< cong -_ p >
        - d
      end

linear-combo-abs : {a b d : Int} -> LinearCombination a b d -> LinearCombination a b (abs d)
linear-combo-abs {a} {b} {d} lc =
  case (split-< 0# d) of
    (\{ (inj-l 0<d) -> subst (LinearCombination a b) (sym (abs-0≤-path (weaken-< 0<d))) lc
      ; (inj-r d≤0) -> subst (LinearCombination a b) (sym (abs-≤0-path d≤0))
                             (linear-combo-negate-result lc)
      })

module _ where
  private
    lc-na : {a b d : Int} -> LinearCombination a b d -> LinearCombination (- a) b d
    lc-na = linear-combo-sym ∘ linear-combo-negate ∘ linear-combo-sym
    lc-nb = linear-combo-negate
    lc-nd = linear-combo-negate-result
    LC = LinearCombination
    lc-a : {a₁ a₂ b d : Int} -> a₁ == a₂ -> LC a₁ b d -> LC a₂ b d
    lc-a p = subst (\a -> LC a _ _) p
    lc-b : {a b₁ b₂ d : Int} -> b₁ == b₂ -> LC a b₁ d -> LC a b₂ d
    lc-b p = subst (\b -> LC _ b _) p
    lc-d : {a b d₁ d₂ : Int} -> d₁ == d₂ -> LC a b d₁ -> LC a b d₂
    lc-d p = subst (\d -> LC _ _ d) p

    linear-combo-unabs-a : {a b d : Int} ->
      LinearCombination (abs a) b d -> LinearCombination a b d
    linear-combo-unabs-a {a = a} lc =
      case (split-< 0# a) of
        (\{ (inj-l 0<a) -> lc-a (abs-0≤-path (weaken-< 0<a)) lc
          ; (inj-r a≤0) -> lc-a (cong -_ (abs-≤0-path a≤0) >=> minus-double-inverse) (lc-na lc)
          })
    linear-combo-unabs-b : {a b d : Int} ->
      LinearCombination a (abs b) d -> LinearCombination a b d
    linear-combo-unabs-b {b = b} lc =
      case (split-< 0# b) of
        (\{ (inj-l 0<b) -> lc-b (abs-0≤-path (weaken-< 0<b)) lc
          ; (inj-r b≤0) -> lc-b (cong -_ (abs-≤0-path b≤0) >=> minus-double-inverse) (lc-nb lc)
          })
    linear-combo-unabs-d : {a b d : Int} ->
      LinearCombination a b (abs d) -> LinearCombination a b d
    linear-combo-unabs-d {d = d} lc =
      case (split-< 0# d) of
        (\{ (inj-l 0<d) -> lc-d (abs-0≤-path (weaken-< 0<d)) lc
          ; (inj-r d≤0) -> lc-d (cong -_ (abs-≤0-path d≤0) >=> minus-double-inverse) (lc-nd lc)
          })

  opaque
    linear-combo-unabs : {a b d : Int} ->
      LinearCombination (abs a) (abs b) (abs d) -> LinearCombination a b d
    linear-combo-unabs lc =
      linear-combo-unabs-a (linear-combo-unabs-b (linear-combo-unabs-d lc))


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
      ==< +-right (+-left (*-left (+-commute >=> +-inverse) >=> *-left-zero)) >
        x * (int a) + (int 0 + y * (int b))
      ==< +-right +-left-zero >
        x * (int a) + y * (int b)
      ==< p >
        (int d)
      end
