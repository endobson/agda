{-# OPTIONS --cubical --safe --exact-split #-}

module ring where

open import base
open import equality
open import nat
import int

private
  variable
    ℓ : Level

record Semiring {ℓ : Level} : Type (ℓ-suc ℓ) where
  infixl 7 _*_
  infixl 6 _+_

  field
    Domain : Set ℓ
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

  +-right-zero : {m : Domain} -> (m + 0#) == m
  +-right-zero {m} = (+-commute {m} {0#}) >=> (+-left-zero {m})

  *-right-zero : {m : Domain} -> (m * 0#) == 0#
  *-right-zero {m} = (*-commute {m} {0#}) >=> (*-left-zero {m})
  *-right-one : {m : Domain} -> (m * 1#) == m
  *-right-one {m} = (*-commute {m} {1#}) >=> (*-left-one {m})

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


record Ring {ℓ : Level} : Type (ℓ-suc ℓ) where
  field
    {{semiring}} : Semiring {ℓ}
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



  private
    lift-constant-nat-helper : Nat -> Domain
    lift-constant-nat-helper zero = 0#
    lift-constant-nat-helper (suc n) = (1# + (lift-constant-nat-helper n))

  lift-constant : int.Int -> Domain
  lift-constant (int.nonneg x) = lift-constant-nat-helper x
  lift-constant (int.neg x) = - lift-constant-nat-helper (suc x)

  minus-lift-constant : {x : int.Int} -> - (lift-constant x) == lift-constant (int.- x)
  minus-lift-constant {int.zero-int} = minus-zero
  minus-lift-constant {int.pos x} = refl
  minus-lift-constant {int.neg x} = minus-double-inverse

NatSemiring : Semiring
NatSemiring = record {
  Domain = Nat;
  0# = 0;
  1# = 1;
  _+_ = _+'_;
  _*_ = _*'_;
  +-assoc = (\ {m} {n} {o} -> (+'-assoc {m} {n} {o}));
  +-commute = (\ {m} {n} -> (+'-commute {m} {n}));
  *-assoc = (\ {m} {n} {o} -> (*'-assoc {m} {n} {o}));
  *-commute = (\ {m} {n} -> (*'-commute {m} {n}));
  +-left-zero = refl;
  *-left-zero = refl;
  *-left-one = +'-right-zero;
  *-distrib-+-right = (\ {m} {n} {o} -> *'-distrib-+' {m} {n} {o}) }

IntSemiring : Semiring
IntSemiring = record {
  Domain = int.Int;
  0# = (int.int 0);
  1# = (int.int 1);
  _+_ = int._+_;
  _*_ = int._*_;
  +-assoc = (\ {m} {n} {o} -> (int.+-assoc {m} {n} {o}));
  +-commute = (\ {m} {n} -> (int.+-commute {m} {n}));
  *-assoc = (\ {m} {n} {o} -> (int.*-assoc {m} {n} {o}));
  *-commute = (\ {m} {n} -> (int.*-commute {m} {n}));
  +-left-zero = refl;
  *-left-zero = refl;
  *-left-one = int.+-right-zero;
  *-distrib-+-right = (\ {m} {n} {o} -> int.*-distrib-+ {m} {n} {o}) }
