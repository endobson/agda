{-# OPTIONS --cubical --safe --exact-split #-}

module ring where

open import base
open import commutative-monoid
open import equality
open import functions
open import group
open import hlevel
open import monoid
open import nat
open import sigma
open import group.int

import int
open int using (ℤ)

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
  +-lift-int {int.nonneg zero} = +-left-zero >=> cong lift-int (sym int.+-left-zero)
  +-lift-int {int.nonneg (suc x)} {y} =
    +-assoc
    >=> +-right (+-lift-int {int.nonneg x} {y})
    >=> sym (+-lift-add1 ((int.nonneg x) int.+ y))
    >=> cong lift-int (sym int.add1-extract-left)
  +-lift-int {int.neg zero} {y} =
    +-left (cong -_ +-right-zero)
    >=> sym (+-lift-sub1 y)
    >=> cong (lift-int ∘ int.sub1) (sym int.+-left-zero)
    >=> cong lift-int (sym int.sub1-extract-left)
  +-lift-int {int.neg (suc x)} {y} =
    +-left minus-distrib-plus >=> +-assoc >=> +-right (+-lift-int {int.neg x} {y})
    >=> sym (+-lift-sub1 ((int.neg x) int.+ y))
    >=> cong lift-int (sym int.sub1-extract-left)

  *-lift-int : {x y : int.Int} -> (lift-int x) * (lift-int y) == (lift-int (x int.* y))
  *-lift-int {int.nonneg zero} = *-left-zero >=> cong lift-int (sym int.*-left-zero)
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
    ==< cong lift-int (sym int.add1-extract-*) >
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
    ==< cong lift-int (cong int.-_ (int.+-right-zero {y}) >=> sym int.+-right-zero) >
      (lift-int ((int.- y) int.+ int.zero-int))
    ==< cong (\x -> (lift-int ((int.- y) int.+ x))) (sym (int.*-left-zero)) >
      (lift-int ((int.- y) int.+ (int.zero-int int.* y)))
    ==< cong lift-int (sym (int.sub1-extract-*)) >
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
    ==< cong lift-int (sym int.sub1-extract-*) >
      (lift-int (int.neg (suc x) int.* y))
    end

  +-Group : GroupStr Domain
  +-Group = record
    { comm-monoid = +-CommMonoid
    ; inverse = -_
    ; ∙-left-inverse = +-commute >=> +-inverse
    }


  -- Units

  record isUnit (x : Domain) : Type ℓ where
    eta-equality
    field
      inv : Domain
      path : (x * inv) == 1#

  is-unit : (x inv : Domain) -> (x * inv) == 1# -> isUnit x
  is-unit _ inv path = record { inv = inv ; path = path }

  isUnit-one : isUnit 1#
  isUnit-one = is-unit 1# 1# *-left-one

  u*-closed : {x y : Domain} -> isUnit x -> isUnit y -> isUnit (x * y)
  u*-closed {x} {y} ux uy = is-unit (x * y) (1/x * 1/y) p
    where
    1/x = isUnit.inv ux
    px = isUnit.path ux
    1/y = isUnit.inv uy
    py = isUnit.path uy

    p : (x * y) * (1/x * 1/y) == 1#
    p = cong (_* (1/x * 1/y)) (*-commute) >=>
        *-assoc >=> (cong (y *_) (sym *-assoc)) >=>
        cong (y *_) (cong (_* 1/y) px >=> *-left-one) >=> py

  isProp-isUnit : {x : Domain} -> isProp (isUnit x)
  isProp-isUnit {x} u1 u2 = (\i -> record
    { inv = inv-path i
    ; path = path-path i
    })
    where
    module u1 = isUnit u1
    module u2 = isUnit u2

    inv-path : u1.inv == u2.inv
    inv-path =
      sym (*-left-one) >=>
      (cong (_* u1.inv) (sym u2.path >=> *-commute)) >=>
      *-assoc >=> *-commute >=>
      (cong (_* u2.inv) u1.path) >=> *-left-one

    path-path : PathP (\i -> x * (inv-path i) == 1#) u1.path u2.path
    path-path = isProp->PathP (\_ -> isSetDomain _ _) u1.path u2.path

  Unit : Type ℓ
  Unit = Σ Domain isUnit

  1u : Unit
  1u = 1# , isUnit-one

  _u*_ : Unit -> Unit -> Unit
  (x , ux) u* (y , uy) = x * y , u*-closed ux uy

  u1/_ : Unit -> Unit
  u1/ (x , u) = u.inv , (is-unit _ x (*-commute >=> u.path))
    where
    module u = isUnit u

  u1/-left-inverse : {x : Unit} -> (u1/ x) u* x == 1u
  u1/-left-inverse {x , u} =
    ΣProp-path isProp-isUnit (*-commute >=> u.path)
    where
    module u = isUnit u

  u1/-right-inverse : {x : Unit} -> x u* (u1/ x) == 1u
  u1/-right-inverse {x , u} =
    ΣProp-path isProp-isUnit u.path
    where
    module u = isUnit u

  u1/-distrib-u* : {x y : Unit} -> u1/ (x u* y) == (u1/ x) u* (u1/ y)
  u1/-distrib-u* {x , ux} {y , uy} = ΣProp-path isProp-isUnit refl


  Monoid-u* : Monoid Unit
  Monoid-u* = record
    { ε = 1u
    ; _∙_ = _u*_
    ; ∙-assoc = ΣProp-path isProp-isUnit *-assoc
    ; ∙-left-ε = ΣProp-path isProp-isUnit *-left-one
    ; ∙-right-ε = ΣProp-path isProp-isUnit *-right-one
    }

  CommMonoid-u* : CommMonoid Unit
  CommMonoid-u* = record
    { monoid = Monoid-u*
    ; ∙-commute = ΣProp-path isProp-isUnit *-commute
    }

  GroupStr-u* : GroupStr Unit
  GroupStr-u* = record
    { comm-monoid = CommMonoid-u*
    ; inverse = u1/_
    ; ∙-left-inverse = u1/-left-inverse
    }

  -- Exponentiation

  _^ℕ_ : Domain -> ℕ -> Domain
  x ^ℕ zero = 1#
  x ^ℕ (suc n) = x * (x ^ℕ n)

  ^ℕ-one : {x : Domain} -> (x ^ℕ 1) == x
  ^ℕ-one = *-right-one

  _u^ℕ_ : Unit -> ℕ -> Unit
  a u^ℕ zero = 1u
  a u^ℕ (suc n) = a u* (a u^ℕ n)


  u^ℕ-one : {x : Unit} -> (x u^ℕ 1) == x
  u^ℕ-one = ΣProp-path isProp-isUnit *-right-one

  u^ℕ-distrib-+' : {b : Unit} {x y : ℕ} -> b u^ℕ (x +' y) == (b u^ℕ x) u* (b u^ℕ y)
  u^ℕ-distrib-+' {b} {zero} {y} =
    cong (b u^ℕ_) (+'-left-zero {y}) >=> sym (Monoid.∙-left-ε Monoid-u*)
  u^ℕ-distrib-+' {b} {suc x} {y} =
    cong (b u*_) (u^ℕ-distrib-+' {b} {x} {y}) >=> sym (Monoid.∙-assoc Monoid-u*)


  _u^ℤ_ : Unit -> ℤ -> Unit
  a u^ℤ (int.nonneg n) = a u^ℕ n
  a u^ℤ (int.neg n) = u1/ (a u^ℕ (suc n))


  u^ℤ-add1 : (u : Unit) (x : ℤ) -> u u^ℤ (int.add1 x) == u u* (u u^ℤ x)
  u^ℤ-add1 u (int.nonneg n) = refl
  u^ℤ-add1 u@(u' , is-u)  (int.neg zero) = path
    where
    module m = CommMonoid CommMonoid-u*
    module is-u = isUnit is-u

    path : 1u == u u* (u1/ (u u^ℕ (suc zero)))
    path = ΣProp-path isProp-isUnit (sym is-u.path) >=> (cong (\x -> (u u* (u1/ x))) (sym u^ℕ-one))
  u^ℤ-add1 u (int.neg (suc n)) = sym path
    where
    path : u u* (u1/ (u u* (u u^ℕ (suc n)))) == (u1/ (u u^ℕ (suc n)))
    path =
      cong (u u*_) (u1/-distrib-u*)
      >=> sym (Monoid.∙-assoc Monoid-u*)
      >=> cong (_u* (u1/ (u u^ℕ (suc n)))) u1/-right-inverse
      >=> Monoid.∙-left-ε Monoid-u*

  u^ℤ-sub1 : (u : Unit) (x : ℤ) -> u u^ℤ (int.sub1 x) == (u1/ u) u* (u u^ℤ x)
  u^ℤ-sub1 u (int.nonneg zero) = ΣProp-path isProp-isUnit refl
  u^ℤ-sub1 u (int.nonneg (suc n)) =
    sym (Monoid.∙-left-ε Monoid-u*) >=>
    cong (_u* (u u^ℤ (int.int n))) (sym (u1/-left-inverse {u})) >=>
    (Monoid.∙-assoc Monoid-u*)
  u^ℤ-sub1 u (int.neg n) =
    cong u1/_ (u^ℤ-add1 u (int.int (suc n))) >=> u1/-distrib-u*


  u^ℤ-preserves-inverse : {b : Unit} {x : ℤ} -> (b u^ℤ (int.- x)) == u1/ (b u^ℤ x)
  u^ℤ-preserves-inverse {x = int.zero-int} = ΣProp-path isProp-isUnit refl
  u^ℤ-preserves-inverse {x = int.pos x} = refl
  u^ℤ-preserves-inverse {x = int.neg x} = ΣProp-path isProp-isUnit refl

  u^ℤ-distrib-+-NonNeg : {b : Unit} {x y : ℤ} -> int.NonNeg x ->
                         b u^ℤ (x int.+ y) == (b u^ℤ x) u* (b u^ℤ y)
  u^ℤ-distrib-+-NonNeg {b} {int.zero-int} _ =
    cong (b u^ℤ_) int.+-left-zero >=> sym (Monoid.∙-left-ε Monoid-u*)
  u^ℤ-distrib-+-NonNeg {b} {int.nonneg (suc x)} {y} _ =
    cong (b u^ℤ_) int.add1-extract-left
    >=> u^ℤ-add1 b ((int.int x) int.+ y)
    >=> cong (b u*_) (u^ℤ-distrib-+-NonNeg {b} {int.nonneg x} {y} tt)
    >=> sym (Monoid.∙-assoc Monoid-u*)
    >=> cong (_u* (b u^ℤ y)) (sym (u^ℤ-add1 b (int.int x)))

  u^ℤ-distrib-+ : {b : Unit} {x y : ℤ} -> b u^ℤ (x int.+ y) == (b u^ℤ x) u* (b u^ℤ y)
  u^ℤ-distrib-+ {b} {x} {y} = int.IntElim-add1sub1-elim z add1-case sub1-case x
    where
    P : ℤ -> Type ℓ
    P x = b u^ℤ (x int.+ y) == (b u^ℤ x) u* (b u^ℤ y)

    z : P (int.int 0)
    z = cong (b u^ℤ_) (int.+-left-zero) >=> sym (Monoid.∙-left-ε Monoid-u*)
    add1-case : (x : ℤ) -> (P x) -> (P (int.add1 x))
    add1-case x p =
      cong (b u^ℤ_) (int.add1-extract-left) >=>
      u^ℤ-add1 b (x int.+ y) >=> cong (b u*_) p >=>
      sym (Monoid.∙-assoc Monoid-u*) >=>
      cong (_u* (b u^ℤ y)) (sym (u^ℤ-add1 b x))

    sub1-case : (x : ℤ) -> (P x) -> (P (int.sub1 x))
    sub1-case x p =
      cong (b u^ℤ_) (int.sub1-extract-left) >=>
      u^ℤ-sub1 b (x int.+ y) >=> cong ((u1/ b) u*_) p >=>
      sym (Monoid.∙-assoc Monoid-u*) >=>
      cong (_u* (b u^ℤ y)) (sym (u^ℤ-sub1 b x))

  Groupʰ-u^ℤ : (base : Unit) -> Groupʰᵉ GroupStr-ℤ+ GroupStr-u* (base u^ℤ_)
  Groupʰ-u^ℤ base = record
    { preserves-ε = refl
    ; preserves-∙ = preserves-∙
    ; preserves-inverse = preserves-inverse
    }
    where
    preserves-∙ : (x y : ℤ) -> (base u^ℤ (x int.+ y)) == (base u^ℤ x) u* (base u^ℤ y)
    preserves-∙ x y = u^ℤ-distrib-+ {base} {x} {y}
    preserves-inverse : (x : ℤ) -> (base u^ℤ (int.- x)) == (u1/ (base u^ℤ x))
    preserves-inverse x = u^ℤ-preserves-inverse {base} {x}


record Semiringʰᵉ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    (S₁ : Semiring D₁) (S₂ : Semiring D₂)
    (f : D₁ -> D₂) : Type (ℓ-max ℓ₁ ℓ₂)
  where
  module S₁ = Semiring S₁
  module S₂ = Semiring S₂

  field
    preserves-1# : f S₁.1# == S₂.1#
    preserves-+ : ∀ x y -> f (x S₁.+ y) == f x S₂.+ f y
    preserves-* : ∀ x y -> f (x S₁.* y) == f x S₂.* f y

Semiringʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{S₁ : Semiring D₁}} {{S₂ : Semiring D₂}}
    (f : D₁ -> D₂) -> Type (ℓ-max ℓ₁ ℓ₂)
Semiringʰ {{S₁ = S₁}} {{S₂ = S₂}} f = Semiringʰᵉ S₁ S₂ f

module Semiringʰ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {S₁ : Semiring D₁} {S₂ : Semiring D₂}
    {f : D₁ -> D₂}
    (s : Semiringʰᵉ S₁ S₂ f) where
  open Semiringʰᵉ s public

Semiringʰ-∘ :
  {ℓ₁ ℓ₂ ℓ₃ : Level}
  {D₁ : Type ℓ₁} {D₂ : Type ℓ₂} {D₃ : Type ℓ₃}
  {S₁ : Semiring D₁} {S₂ : Semiring D₂} {S₃ : Semiring D₃}
  {f : D₂ -> D₃} {g : D₁ -> D₂} ->
  (Semiringʰ {{S₂}} {{S₃}} f) ->
  (Semiringʰ {{S₁}} {{S₂}} g) ->
  (Semiringʰ {{S₁}} {{S₃}} (f ∘ g))
Semiringʰ-∘ {S₁ = S₁} {S₂} {S₃} {f} {g} f' g' = record
  { preserves-1# = (cong f g'.preserves-1#) >=> f'.preserves-1#
  ; preserves-+ =
    (\x y -> (cong f (g'.preserves-+ x y)) >=> f'.preserves-+ (g x) (g y))
  ; preserves-* =
    (\x y -> (cong f (g'.preserves-* x y)) >=> f'.preserves-* (g x) (g y))
  }
  where
  module f' = Semiringʰ f'
  module g' = Semiringʰ g'


record Ringʰᵉ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    (R₁ : Ring D₁) (R₂ : Ring D₂)
    (f : D₁ -> D₂) : Type (ℓ-max ℓ₁ ℓ₂)
  where
  module R₁ = Ring R₁
  module R₂ = Ring R₂

  field
    preserves-0# : f R₁.0# == R₂.0#
    preserves-1# : f R₁.1# == R₂.1#
    preserves-+ : ∀ x y -> f (x R₁.+ y) == f x R₂.+ f y
    preserves-* : ∀ x y -> f (x R₁.* y) == f x R₂.* f y
    preserves-minus : ∀ x -> f (R₁.- x) == R₂.- (f x)


Ringʰ :
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {{R₁ : Ring D₁}} {{R₂ : Ring D₂}}
    (f : D₁ -> D₂) -> Type (ℓ-max ℓ₁ ℓ₂)
Ringʰ {{R₁ = R₁}} {{R₂ = R₂}} f = Ringʰᵉ R₁ R₂ f

module Ringʰ
    {ℓ₁ ℓ₂ : Level}
    {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
    {R₁ : Ring D₁} {R₂ : Ring D₂}
    {f : D₁ -> D₂}
    (s : Ringʰᵉ R₁ R₂ f) where
  open Ringʰᵉ s public
