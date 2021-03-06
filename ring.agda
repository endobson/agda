{-# OPTIONS --cubical --safe --exact-split #-}

module ring where

open import base
open import equality
open import monoid
open import commutative-monoid
open import nat
open import hlevel

import int

private
  variable
    ℓ : Level
    A : Set ℓ


record Semiring {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  infixl 7 _*_
  infixl 6 _+_

  field
    0# : Domain
    1# : Domain
    _+_ : Domain -> Domain -> Domain
    _*_ : Domain -> Domain -> Domain
    +-assoc : {m n o : Domain} -> (m + n) + o == m + (n + o)
    +-commute : {m n : Domain} -> (m + n) == (n + m)
    *-assoc : {m n o : Domain} -> (m * n) * o == m * (n * o)
    *-commute : {m n : Domain} -> (m * n) == (n * m)
    +-left-zero : {m : Domain} -> (0# + m) == m
    *-left-zero : {m : Domain} -> (0# * m) == 0#
    *-left-one : {m : Domain} -> (1# * m) == m
    *-distrib-+-right : {m n o : Domain} -> (m + n) * o == (m * o) + (n * o)
    isSetDomain : isSet Domain

  +-right-zero : {m : Domain} -> (m + 0#) == m
  +-right-zero {m} = (+-commute {m} {0#}) >=> (+-left-zero {m})

  *-right-zero : {m : Domain} -> (m * 0#) == 0#
  *-right-zero {m} = (*-commute {m} {0#}) >=> (*-left-zero {m})
  *-right-one : {m : Domain} -> (m * 1#) == m
  *-right-one {m} = (*-commute {m} {1#}) >=> (*-left-one {m})

  instance
    +-Monoid : Monoid Domain
    +-Monoid = record
      { ε = 0#
      ; _∙_ = _+_
      ; ∙-assoc = (\ {m} {n} {o} -> +-assoc {m} {n} {o})
      ; ∙-left-ε = (\ {m} -> +-left-zero {m})
      ; ∙-right-ε = (\ {m} -> +-right-zero {m})
      }

    +-CommMonoid : CommMonoid Domain
    +-CommMonoid = record
      { ∙-commute = +-commute
      }

    *-Monoid : Monoid Domain
    *-Monoid = record
      { ε = 1#
      ; _∙_ = _*_
      ; ∙-assoc = (\ {m} {n} {o} -> *-assoc {m} {n} {o})
      ; ∙-left-ε = (\ {m} -> *-left-one {m})
      ; ∙-right-ε = (\ {m} -> *-right-one {m})
      }

    *-CommMonoid : CommMonoid Domain
    *-CommMonoid = record
      { ∙-commute = *-commute
      }


  *-distrib-+-left : {m n o : Domain} -> m * (n + o) == (m * n) + (m * o)
  *-distrib-+-left {m} {n} {o} =
    begin
      m * (n + o)
    ==< (*-commute {m} {n + o}) >
      (n + o) * m
    ==< (*-distrib-+-right {n} {o} {m}) >
      n * m + o * m
    ==< (cong2 _+_ (*-commute {n} {m}) (*-commute {o} {m})) >
      (m * n) + (m * o)
    end

  +-right : {m n p : Domain} -> (n == p) -> m + n == m + p
  +-right {m} id = cong (\x -> m + x) id

  +-left : {m n p : Domain} -> (n == p) -> n + m == p + m
  +-left {m} id = cong (\x -> x + m) id

  +-cong : {m n p o : Domain} -> m == p -> n == o -> m + n == p + o
  +-cong = cong2 _+_

  *-right : {m n p : Domain} -> (n == p) -> m * n == m * p
  *-right {m} id = cong (\x -> m * x) id

  *-left : {m n p : Domain} -> (n == p) -> n * m == p * m
  *-left {m} id = cong (\x -> x * m) id

  *-cong : {m n p o : Domain} -> m == p -> n == o -> m * n == p * o
  *-cong = cong2 _*_



record Ring {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    {{semiring}} : Semiring Domain
  open Semiring semiring public

  field
    -_ : Domain -> Domain
    +-inverse : {x : Domain } -> (x + (- x)) == 0#

  minus-zero : (- 0#) == 0#
  minus-zero =
    begin
      (- 0#)
    ==< sym +-left-zero >
      0# + (- 0#)
    ==< +-inverse >
      0#
    end

  minus-unique : {a b : Domain} -> a + b == 0# -> b == - a
  minus-unique {a} {b} pr =
    begin
      b
    ==< sym +-left-zero >
      0# + b
    ==< +-left (sym +-inverse) >
      (a + - a) + b
    ==< +-left +-commute >
      (- a + a) + b
    ==< +-assoc >
      - a + (a + b)
    ==< +-right pr >
      - a + 0#
    ==< +-right-zero  >
      - a
    end

  *-left-minus-one : {a : Domain} -> (- 1#) * a == - a
  *-left-minus-one {a} =
    begin
      - 1# * a
    ==< sym +-left-zero >
      0# + - 1# * a
    ==< +-left (sym +-inverse) >
      (a + - a) + - 1# * a
    ==< +-left +-commute >
      (- a + a) + - 1# * a
    ==< +-assoc >
      - a + (a + - 1# * a)
    ==< +-right (+-left (sym *-left-one)) >
      - a + (1# * a + - 1# * a)
    ==< +-right (sym *-distrib-+-right) >
      - a + ((1# + - 1#) * a)
    ==< +-right (*-left +-inverse) >
      - a + (0# * a)
    ==< +-right *-left-zero >
      - a + 0#
    ==< +-right-zero >
      - a
    end

  minus-extract-left : {a b : Domain} -> (- a * b) == - (a * b)
  minus-extract-left {a} {b} =
    begin
      - a * b
    ==< *-left (sym *-left-minus-one) >
      (- 1# * a) * b
    ==< *-assoc >
      - 1# * (a * b)
    ==< *-left-minus-one >
      - (a * b)
    end

  minus-distrib-plus : {a b : Domain} -> - (a + b) == - a + - b
  minus-distrib-plus {a} {b} =
    begin
      - (a + b)
    ==< sym *-left-minus-one >
      - 1# * (a + b)
    ==< *-distrib-+-left >
      - 1# * a + - 1# * b
    ==< +-left *-left-minus-one >
      - a + - 1# * b
    ==< +-right *-left-minus-one >
      - a + - b
    end

  minus-double-inverse : {a : Domain} -> - - a == a
  minus-double-inverse {a} = sym (minus-unique
    (begin
       - a + a
     ==< +-commute >
       a + - a
     ==< +-inverse >
       0#
     end))


  lift-nat : Nat -> Domain
  lift-nat zero = 0#
  lift-nat (suc n) = (1# + (lift-nat n))

  lift-int : int.Int -> Domain
  lift-int (int.nonneg x) = lift-nat x
  lift-int (int.neg x) = - lift-nat (suc x)

  minus-lift-constant : {x : int.Int} -> - (lift-int x) == lift-int (int.- x)
  minus-lift-constant {int.zero-int} = minus-zero
  minus-lift-constant {int.pos x} = refl
  minus-lift-constant {int.neg x} = minus-double-inverse

  +-lift-nat : {x y : Nat} -> (lift-nat x) + (lift-nat y) == (lift-nat (x +' y))
  +-lift-nat {zero} = +-left-zero
  +-lift-nat {suc n} =  +-assoc >=> (+-right (+-lift-nat {n}))

  private
    +-lift-add1 : ∀ x -> (lift-int (int.add1 x)) == 1# + (lift-int x)
    +-lift-add1 (int.nonneg x) = refl
    +-lift-add1 (int.neg zero) = sym (+-right (cong -_ +-right-zero) >=> +-inverse)
    +-lift-add1 (int.neg (suc x)) = sym
      (begin
         1# + (lift-int (int.neg (suc x)))
       ==<>
         1# + - (1# + (lift-nat (suc x)))
       ==< +-right minus-distrib-plus >
         1# + (- 1# + - (lift-nat (suc x)))
       ==< sym +-assoc >
         (1# + - 1#) + - (lift-nat (suc x))
       ==< +-left +-inverse >
         0# + - (lift-nat (suc x))
       ==< +-left-zero >
         (lift-int (int.neg x))
       end)

    +-lift-sub1 : ∀ x -> (lift-int (int.sub1 x)) == - 1# + (lift-int x)
    +-lift-sub1 (int.neg x) = minus-distrib-plus
    +-lift-sub1 (int.nonneg zero) =
      sym( +-right-zero >=> cong -_ (sym +-right-zero))
    +-lift-sub1 (int.nonneg (suc x)) = sym
      (begin
         - 1# + (lift-int (int.nonneg (suc x)))
       ==<>
         - 1# + (1# + (lift-int (int.nonneg x)))
       ==< sym +-assoc >
         (- 1# + 1#) + (lift-int (int.nonneg x))
       ==< +-left +-commute >
         (1# + - 1#) + (lift-int (int.nonneg x))
       ==< +-left +-inverse >
         0# + (lift-int (int.nonneg x))
       ==< +-left-zero >
         (lift-int (int.nonneg x))
       end)

  +-lift-int : {x y : int.Int} -> (lift-int x) + (lift-int y) == (lift-int (x int.+ y))
  +-lift-int {int.nonneg zero} = +-left-zero
  +-lift-int {int.nonneg (suc x)} {y} =
    +-assoc >=> +-right (+-lift-int {int.nonneg x} {y}) >=> sym (+-lift-add1 ((int.nonneg x) int.+ y))
  +-lift-int {int.neg zero} {y} =
    +-left (cong -_ +-right-zero) >=> sym (+-lift-sub1 y)
  +-lift-int {int.neg (suc x)} {y} =
    +-left minus-distrib-plus >=> +-assoc >=> +-right (+-lift-int {int.neg x} {y})
    >=> sym (+-lift-sub1 ((int.neg x) int.+ y))

  *-lift-int : {x y : int.Int} -> (lift-int x) * (lift-int y) == (lift-int (x int.* y))
  *-lift-int {int.nonneg zero} = *-left-zero
  *-lift-int {int.nonneg (suc x)} {y} =
    begin
      (lift-int (int.nonneg (suc x))) * (lift-int y)
    ==<>
      (1# + (lift-int (int.nonneg x))) * (lift-int y)
    ==< *-distrib-+-right >
      1# * (lift-int y) + (lift-int (int.nonneg x)) * (lift-int y)
    ==< +-left *-left-one >
      (lift-int y) + (lift-int (int.nonneg x)) * (lift-int y)
    ==< +-right (*-lift-int {int.nonneg x} {y}) >
      (lift-int y) + (lift-int ((int.nonneg x) int.* y))
    ==< +-lift-int {y} {(int.nonneg x) int.* y} >
      (lift-int (y int.+ (int.nonneg x) int.* y))
    ==<>
      (lift-int (int.nonneg (suc x) int.* y))
    end
  *-lift-int {int.neg zero} {y} =
    begin
      (lift-int (int.neg zero)) * (lift-int y)
    ==<>
      - (1# + 0#) * (lift-int y)
    ==< *-left (cong -_ +-right-zero) >
     - 1# * (lift-int y)
    ==< *-left-minus-one >
      - (lift-int y)
    ==< (minus-lift-constant {y}) >
      (lift-int (int.- y))
    ==< cong lift-int (cong int.-_ (sym (int.+-right-zero {y}))) >
      (lift-int (int.- (y int.+ int.zero-int)))
    ==<>
      (lift-int ((int.neg zero) int.* y))
    end
  *-lift-int {int.neg (suc x)} {y} =
    begin
      (lift-int (int.neg (suc x))) * (lift-int y)
    ==<>
      - (1# + (lift-nat (suc x))) * (lift-int y)
    ==< *-left minus-distrib-plus >
     (- 1# + (lift-int (int.neg x))) * (lift-int y)
    ==< *-distrib-+-right >
      - 1# * (lift-int y) + (lift-int (int.neg x)) * (lift-int y)
    ==< +-left *-left-minus-one >
      - (lift-int y) + (lift-int (int.neg x)) * (lift-int y)
    ==< +-left (minus-lift-constant {y}) >
      (lift-int (int.- y)) + (lift-int (int.neg x)) * (lift-int y)
    ==< +-right (*-lift-int {int.neg x} {y}) >
      (lift-int (int.- y)) + (lift-int ((int.neg x) int.* y))
    ==< +-lift-int {int.- y} {(int.neg x) int.* y} >
      (lift-int ((int.- y) int.+ (int.neg x) int.* y))
    ==< cong lift-int (sym (int.minus-distrib-+ {y} {int.pos x int.* y})) >
      (lift-int (int.- (y int.+ (int.pos x) int.* y)))
    ==<>
      (lift-int (int.neg (suc x) int.* y))
    end
