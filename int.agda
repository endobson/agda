{-# OPTIONS --cubical --safe --exact-split #-}

module int where

open import equality
open import base
open import nat
open import monoid
open import hlevel
open import relation

data Int : Set where
 -- nonneg n Corresponds to n
 nonneg : Nat -> Int
 -- neg n Corresponds to -(n+1)
 neg : Nat -> Int

pattern zero-int = nonneg zero
pattern pos x = nonneg (suc x)

int : Nat -> Int
int = nonneg

-- Sign based predicates

Zero : (n : Int) -> Set
Zero zero-int = Top
Zero (pos x) = Bot
Zero (neg x) = Bot

Pos : (n : Int) -> Set
Pos zero-int = Bot
Pos (pos x) = Top
Pos (neg x) = Bot

Neg : (n : Int) -> Set
Neg (nonneg x) = Bot
Neg (neg x) = Top

NonZero : (n : Int) -> Set
NonZero zero-int = Bot
NonZero (pos x) = Top
NonZero (neg x) = Top

NonPos : (n : Int) -> Set
NonPos zero-int = Top
NonPos (pos x) = Bot
NonPos (neg x) = Top

NonNeg : (n : Int) -> Set
NonNeg (nonneg x) = Top
NonNeg (neg x) = Bot

-- The sign based predicates are propositions

isPropZero : {n : Int} -> isProp (Zero n)
isPropZero {zero-int} _ _ = refl
isPropZero {pos _} ()
isPropZero {neg _} ()

isPropPos : {n : Int} -> isProp (Pos n)
isPropPos {zero-int} ()
isPropPos {pos _} _ _ = refl
isPropPos {neg _} ()

isPropNeg : {n : Int} -> isProp (Neg n)
isPropNeg {zero-int} ()
isPropNeg {pos _} ()
isPropNeg {neg _} _ _ = refl

isPropNonZero : {n : Int} -> isProp (NonZero n)
isPropNonZero {zero-int} ()
isPropNonZero {pos _} _ _ = refl
isPropNonZero {neg _} _ _ = refl

isPropNonPos : {n : Int} -> isProp (NonPos n)
isPropNonPos {zero-int} _ _ = refl
isPropNonPos {pos _} ()
isPropNonPos {neg _} _ _ = refl

isPropNonNeg : {n : Int} -> isProp (NonNeg n)
isPropNonNeg {zero-int} _ _ = refl
isPropNonNeg {pos _} _ _ = refl
isPropNonNeg {neg _} ()

-- Weakening of the predicates

Pos->NonNeg : {n : Int} -> .(Pos n) -> NonNeg n
Pos->NonNeg {pos n} _ = tt

Pos->NonZero : {n : Int} -> .(Pos n) -> NonZero n
Pos->NonZero {pos x} _ = tt

Neg->NonPos : {n : Int} -> .(Neg n) -> NonPos n
Neg->NonPos {neg n} _ = tt

Neg->NonZero : {n : Int} -> .(Neg n) -> NonZero n
Neg->NonZero {neg x} _ = tt

-- The predicates are negations of others

NonNeg->¬Neg : {n : Int} -> .(NonNeg n) -> ¬(Neg n)
NonNeg->¬Neg {nonneg _} _ ()
NonNeg->¬Neg {neg _} ()

NonPos->¬Pos : {n : Int} -> .(NonPos n) -> ¬(Pos n)
NonPos->¬Pos {zero-int} _ ()
NonPos->¬Pos {neg _} _ ()
NonPos->¬Pos {pos _} ()


infix 9 -_
-_ : Int -> Int
- zero-int = zero-int
- (pos n) = neg n
- (neg n) = pos n

minus : Int -> Int
minus = -_

minus-double-inverse : {x : Int} -> - - x == x
minus-double-inverse {zero-int} = refl
minus-double-inverse {pos x'} = refl
minus-double-inverse {neg x'} = refl

minus-injective : {x y : Int} -> - x == - y -> x == y
minus-injective p = sym minus-double-inverse >=> cong (-_) p >=> minus-double-inverse

add1 : Int -> Int
add1 (nonneg x) = (nonneg (suc x))
add1 (neg x) = - (nonneg x)

sub1 : Int -> Int
sub1 (nonneg zero) = neg zero
sub1 (nonneg (suc n)) = nonneg n
sub1 (neg n) = (neg (suc n))

infixl 6 _+_
_+_ : Int -> Int -> Int
(nonneg m) + n = (rec m)
  where rec : Nat -> Int
        rec zero = n
        rec (suc m) = add1 ((nonneg m) + n)
(neg m) + n = sub1 (rec m)
  where rec : Nat -> Int
        rec zero = n
        rec (suc m) = (neg m) + n

add1-sub1-id : {n : Int} -> add1 (sub1 n) == n
add1-sub1-id {zero-int} = refl
add1-sub1-id {pos n'} = refl
add1-sub1-id {neg n'} = refl

sub1-add1-id : {n : Int} -> sub1 (add1 n) == n
sub1-add1-id {nonneg n} = refl
sub1-add1-id {neg zero} = refl
sub1-add1-id {neg (suc n')} = refl

add1-extract-left : {m n : Int} -> add1 m + n == add1 (m + n)
sub1-extract-left : {m n : Int} -> sub1 m + n == sub1 (m + n)
add1-extract-left {nonneg m'} = refl
add1-extract-left {neg zero} {n} = (sym (add1-sub1-id {n}))
add1-extract-left {neg (suc m')} {n} =
  begin
    add1 (neg (suc m')) + n
  ==<>
    neg m' + n
  ==< sym (add1-sub1-id {neg m' + n}) >
    add1 (sub1 (neg m' + n))
  ==< cong add1 (sym (sub1-extract-left {neg m'})) >
    add1 (sub1 (neg m') + n)
  ==<>
    add1 ((neg (suc m')) + n)
  end

sub1-extract-left {zero-int} = refl
sub1-extract-left {neg m'} = refl
sub1-extract-left {nonneg (suc m')} {n} =
  begin
   sub1 (nonneg (suc m')) + n
  ==<>
   nonneg m' + n
  ==< sym (sub1-add1-id {nonneg m' + n}) >
   sub1 (add1 (nonneg m' + n))
  ==< cong sub1 (sym (add1-extract-left {nonneg m'})) >
   sub1 (add1 (nonneg m') + n)
  ==<>
   sub1 ((nonneg (suc m')) + n)
  end

+-right : {m n p : Int} -> (n == p) -> m + n == m + p
+-right {m} id = cong (\x -> m + x) id

+-left : {m n p : Int} -> (n == p) -> n + m == p + m
+-left {m} id = cong (\x -> x + m) id

+-assoc : {m n o : Int} -> (m + n) + o == m + (n + o)
+-assoc {zero-int} = refl
+-assoc {pos zero} {n} {o} = add1-extract-left {n} {o}
+-assoc {neg zero} {n} {o} = sub1-extract-left {n} {o}
+-assoc {pos (suc m')} {n} {o} =
  begin
    (pos (suc m') + n) + o
  ==<>
    (add1 (pos m') + n) + o
  ==< +-left (add1-extract-left {pos m'}) >
    (add1 (pos m' + n)) + o
  ==< add1-extract-left {pos m' + n} >
    add1 ((pos m' + n) + o)
  ==< cong add1 (+-assoc {pos m'}) >
    add1 (pos m' + (n + o))
  ==<>
    pos (suc m') + (n + o)
  end
+-assoc {neg (suc m')} {n} {o} =
  begin
    (neg (suc m') + n) + o
  ==<>
    (sub1 (neg m') + n) + o
  ==< +-left (sub1-extract-left {neg m'}) >
    (sub1 (neg m' + n)) + o
  ==< sub1-extract-left {neg m' + n} >
    sub1 ((neg m' + n) + o)
  ==< cong sub1 (+-assoc {neg m'}) >
    sub1 (neg m' + (n + o))
  ==<>
    neg (suc m') + (n + o)
  end

+-right-zero : {m : Int} -> (m + zero-int) == m
+-right-zero {nonneg zero} = refl
+-right-zero {neg zero} = refl
+-right-zero {nonneg (suc m)} =
  begin
    (nonneg (suc m) + zero-int)
  ==<>
    add1 (nonneg m + zero-int)
  ==< cong add1 (+-right-zero {nonneg m}) >
    add1 (nonneg m)
  ==<>
    nonneg (suc m)
  end
+-right-zero {neg (suc m)} =
  begin
    (neg (suc m) + zero-int)
  ==<>
    sub1 (neg m + zero-int)
  ==< cong sub1 (+-right-zero {neg m}) >
    sub1 (neg m)
  ==<>
    neg (suc m)
  end

+-left-zero : {m : Int} -> (zero-int + m) == m
+-left-zero = refl


add1-extract-right : {m n : Int} -> m + add1 n == add1 (m + n)
add1-extract-right {nonneg zero} {n} = refl
add1-extract-right {nonneg (suc m')} {n} = cong add1 (add1-extract-right {nonneg m'})
add1-extract-right {neg zero} {n} = (sub1-add1-id {n}) >=> (sym (add1-sub1-id {n}))
add1-extract-right {neg (suc m')} {n} =
  begin
    neg (suc m') + add1 n
  ==<>
    sub1 (neg m') + add1 n
  ==< sub1-extract-left {neg m'}  >
    sub1 (neg m' + add1 n)
  ==< cong sub1 (add1-extract-right {neg m'}) >
    sub1 (add1 (neg m' + n))
  ==< sub1-add1-id >
    neg m' + n
  ==< sym add1-sub1-id >
    add1 (sub1 (neg m' + n))
  ==< cong add1 (sym (sub1-extract-left {neg m'})) >
    add1 (sub1 (neg m') + n)
  ==<>
    (add1 (neg (suc m') + n))
  end

sub1-extract-right : {m n : Int} -> m + sub1 n == sub1 (m + n)
sub1-extract-right {neg zero} {n} = refl
sub1-extract-right {neg (suc m')} {n} = cong sub1 (sub1-extract-right {neg m'})
sub1-extract-right {nonneg zero} {n} = refl
sub1-extract-right {nonneg (suc m')} {n} =
  begin
    nonneg (suc m') + sub1 n
  ==<>
    add1 (nonneg m') + sub1 n
  ==< add1-extract-left {nonneg m'}  >
    add1 (nonneg m' + sub1 n)
  ==< cong add1 (sub1-extract-right {nonneg m'}) >
    add1 (sub1 (nonneg m' + n))
  ==< add1-sub1-id >
    nonneg m' + n
  ==< sym sub1-add1-id >
    sub1 (add1 (nonneg m' + n))
  ==< cong sub1 (sym (add1-extract-left {nonneg m'})) >
    sub1 (add1 (nonneg m') + n)
  ==<>
    (sub1 (nonneg (suc m') + n))
  end

+-commute : {m n : Int} -> (m + n) == (n + m)
+-commute {nonneg zero} {n} = sym (+-right-zero {n})
+-commute {neg zero} {n} =
 begin
   neg zero + n
 ==<>
   sub1 n
 ==< cong sub1 (sym (+-right-zero {n})) >
   sub1 (n + zero-int)
 ==< sym (sub1-extract-right {n}) >
   n + sub1 zero-int
 ==<>
   n + neg zero
 end
+-commute {nonneg (suc m')} {n} =
  begin
    nonneg (suc m') + n
  ==<>
    add1 (nonneg m' + n)
  ==< cong add1 (+-commute {nonneg m'}) >
    add1 (n + nonneg m')
  ==< sym (add1-extract-right {n})>
    n + add1 (nonneg m')
  ==<>
    n + nonneg (suc m')
  end
+-commute {neg (suc m')} {n} =
  begin
    neg (suc m') + n
  ==<>
    sub1 (neg m' + n)
  ==< cong sub1 (+-commute {neg m'}) >
    sub1 (n + neg m')
  ==< sym (sub1-extract-right {n})>
    n + sub1 (neg m')
  ==<>
    n + neg (suc m')
  end

+-left-injective : (m : Int) {n p : Int} -> (m + n) == (m + p) -> n == p
+-left-injective zero-int      path = path
+-left-injective (pos zero)    path = sym sub1-add1-id >=> cong sub1 path >=> sub1-add1-id
+-left-injective (pos (suc n)) path =
  +-left-injective (pos n) (sym sub1-add1-id >=> cong sub1 path >=> sub1-add1-id)
+-left-injective (neg zero)    path = sym add1-sub1-id >=> cong add1 path >=> add1-sub1-id
+-left-injective (neg (suc n)) path =
  +-left-injective (neg n) (sym add1-sub1-id >=> cong add1 path >=> add1-sub1-id)

+-right-injective : {m : Int} (n : Int) {p : Int} -> (m + n) == (p + n) -> m == p
+-right-injective {m} n {p} path =
  +-left-injective n (+-commute {n} {m} >=> path >=> +-commute {p} {n})

add1-NonNeg : {n : Int} -> .(NonNeg n) -> (Pos (add1 n))
add1-NonNeg {nonneg _} _ = tt

add1-Pos : {n : Int} -> .(Pos n) -> (Pos (add1 n))
add1-Pos {pos _} _ = tt

sub1-NonPos : {n : Int} -> .(NonPos n) -> (Neg (sub1 n))
sub1-NonPos {zero-int} _ = tt
sub1-NonPos {neg _} _ = tt

sub1-Neg : {n : Int} -> .(Neg n) -> (Neg (sub1 n))
sub1-Neg {neg _} _ = tt


+-Pos-NonNeg : {m n : Int} -> .(Pos m) -> .(NonNeg n) -> Pos (m + n)
+-Pos-NonNeg {pos zero} _ p = add1-NonNeg p
+-Pos-NonNeg {pos (suc m)} _ p = add1-Pos (+-Pos-NonNeg {pos m} tt p)

+-NonNeg-Pos : {m n : Int} -> .(NonNeg m) -> .(Pos n) -> Pos (m + n)
+-NonNeg-Pos {m} {n} p1 p2 = subst Pos (+-commute {n} {m}) (+-Pos-NonNeg p2 p1)

+-Pos-Pos : {m n : Int} -> .(Pos m) -> .(Pos n) -> Pos (m + n)
+-Pos-Pos p1 p2 = +-Pos-NonNeg p1 (Pos->NonNeg p2)

+-Neg-NonPos : {m n : Int} -> .(Neg m) -> .(NonPos n) -> Neg (m + n)
+-Neg-NonPos {neg zero} _ p = sub1-NonPos p
+-Neg-NonPos {neg (suc m)} _ p = sub1-Neg (+-Neg-NonPos {neg m} tt p)

+-NonPos-Neg : {m n : Int} -> .(NonPos m) -> .(Neg n) -> Neg (m + n)
+-NonPos-Neg {m} {n} p1 p2 = subst Neg (+-commute {n} {m}) (+-Neg-NonPos p2 p1)

+-Neg-Neg : {m n : Int} -> .(Neg m) -> .(Neg n) -> Neg (m + n)
+-Neg-Neg p1 p2 = +-Neg-NonPos p1 (Neg->NonPos p2)

+-NonNeg-NonNeg : {m n : Int} -> .(NonNeg m) -> .(NonNeg n) -> NonNeg (m + n)
+-NonNeg-NonNeg {zero-int} {zero-int} p1 p2 = tt
+-NonNeg-NonNeg {zero-int} {pos n} p1 p2 =
  Pos->NonNeg {zero-int + pos n} (+-NonNeg-Pos {zero-int} {pos n} tt tt)
+-NonNeg-NonNeg {pos m} {zero-int} p1 p2 =
  Pos->NonNeg {pos m + zero-int} (+-Pos-NonNeg {pos m} {zero-int} tt tt)
+-NonNeg-NonNeg {pos m} {pos n} p1 p2 =
  Pos->NonNeg {pos m + pos n} (+-Pos-Pos {pos m} {pos n} tt tt)

+-NonPos-NonPos : {m n : Int} -> .(NonPos m) -> .(NonPos n) -> NonPos (m + n)
+-NonPos-NonPos {zero-int} {zero-int} p1 p2 = tt
+-NonPos-NonPos {zero-int} {neg n} p1 p2 =
  Neg->NonPos {zero-int + neg n} (+-NonPos-Neg {zero-int} {neg n} tt tt)
+-NonPos-NonPos {neg m} {zero-int} p1 p2 =
  Neg->NonPos {neg m + zero-int} (+-Neg-NonPos {neg m} {zero-int} tt tt)
+-NonPos-NonPos {neg m} {neg n} p1 p2 =
  Neg->NonPos {neg m + neg n} (+-Neg-Neg {neg m} {neg n} tt tt)

minus-Pos : {n : Int} -> .(Pos n) -> Neg (- n)
minus-Pos {pos _} _ = tt

minus-Neg : {n : Int} -> .(Neg n) -> Pos (- n)
minus-Neg {neg _} _ = tt

minus-NonPos : {n : Int} -> .(NonPos n) -> NonNeg (- n)
minus-NonPos {zero-int} _ = tt
minus-NonPos {neg _}    _ = tt

minus-NonNeg : {n : Int} -> .(NonNeg n) -> NonPos (- n)
minus-NonNeg {zero-int} _ = tt
minus-NonNeg {pos _}    _ = tt


add1-minus->minus-sub1 : {n : Int} -> add1 (- n) == - (sub1 n)
add1-minus->minus-sub1 {neg _} = refl
add1-minus->minus-sub1 {nonneg zero} = refl
add1-minus->minus-sub1 {nonneg (suc n)} = refl

sub1-minus->minus-add1 : {n : Int} -> sub1 (- n) == - (add1 n)
sub1-minus->minus-add1 {nonneg zero} = refl
sub1-minus->minus-add1 {nonneg (suc n')} = refl
sub1-minus->minus-add1 {neg zero} = refl
sub1-minus->minus-add1 {neg (suc n')} = refl


add-minus-zero : {n : Int} -> n + - n == zero-int
add-minus-zero {zero-int} = refl
add-minus-zero {pos zero} = refl
add-minus-zero {neg zero} = refl
add-minus-zero {pos (suc n')} =
  begin
    pos (suc n') + - pos (suc n')
  ==<>
    add1 (pos n') + - add1 (pos n')
  ==< add1-extract-left {pos n'} >
    add1 ((pos n') + - add1 (pos n'))
  ==< sym (add1-extract-right {pos n'}) >
    (pos n') + add1 (- add1 (pos n'))
  ==< +-right {pos n'} (add1-minus->minus-sub1 {add1 (pos n')}) >
    (pos n') + - (sub1 (add1 (pos n')))
  ==< +-right {pos n'} (cong minus (sub1-add1-id)) >
    pos n' + - pos n'
  ==< add-minus-zero {pos n'}  >
    zero-int
  end
add-minus-zero {neg (suc n')} =
  begin
    neg (suc n') + - neg (suc n')
  ==<>
    sub1 (neg n') + - sub1 (neg n')
  ==< sub1-extract-left {neg n'} >
    sub1 ((neg n') + - sub1 (neg n'))
  ==< sym (sub1-extract-right {neg n'}) >
    (neg n') + sub1 (- sub1 (neg n'))
  ==< +-right {neg n'} (sub1-minus->minus-add1 {sub1 (neg n')}) >
    (neg n') + - (add1 (sub1 (neg n')))
  ==< +-right {neg n'} (cong minus (add1-sub1-id {neg n'})) >
    neg n' + - neg n'
  ==< add-minus-zero {neg n'}  >
    zero-int
  end

minus-distrib-+ : {m n : Int} -> - (m + n) == - m + - n
minus-distrib-+ {zero-int} = refl
minus-distrib-+ {pos zero} {n} = sym (sub1-minus->minus-add1 {n})
minus-distrib-+ {neg zero} {n} = sym (add1-minus->minus-sub1 {n})
minus-distrib-+ {pos (suc m')} {n} =
  begin
    - (pos (suc m') + n)
  ==<>
    - (add1 (pos m' + n))
  ==< sym (sub1-minus->minus-add1 {pos m' + n}) >
    sub1 (- (pos m' + n))
  ==< cong sub1 (minus-distrib-+ {pos m'}) >
    sub1 (- pos m' + - n)
  ==< sym (sub1-extract-left { - pos m'}) >
    sub1 (- (pos m')) + - n
  ==< +-left (sub1-minus->minus-add1 {pos m'}) >
    - (add1 (pos m')) + - n
  ==<>
    - (pos (suc m')) + - n
  end
minus-distrib-+ {neg (suc m')} {n} =
  begin
    - (neg (suc m') + n)
  ==<>
    - (sub1 (neg m' + n))
  ==< sym (add1-minus->minus-sub1 {neg m' + n}) >
    add1 (- (neg m' + n))
  ==< cong add1 (minus-distrib-+ {neg m'}) >
    add1 (- neg m' + - n)
  ==< sym (add1-extract-left { - neg m'}) >
    add1 (- (neg m')) + - n
  ==< +-left (add1-minus->minus-sub1 {neg m'}) >
    - (sub1 (neg m')) + - n
  ==<>
    - (neg (suc m')) + - n
  end


infixl 7 _*nz_
_*nz_ : Nat -> Int -> Int
zero *nz m = zero-int
suc n *nz m = m + n *nz m


infixl 7 _*_
_*_ : Int -> Int -> Int
nonneg m * n = m *nz n
neg m * n = -(suc m *nz n)

*-right : {m n p : Int} -> (n == p) -> m * n == m * p
*-right {m} id = cong (\x -> m * x) id

*-left : {m n p : Int} -> (n == p) -> n * m == p * m
*-left {m} id = cong (\x -> x * m) id

minus-extract-left : {m n : Int} -> - m * n == - (m * n)
minus-extract-left {zero-int} = refl
minus-extract-left {pos m'} = refl
minus-extract-left {neg m'} {n} = sym (minus-double-inverse {pos m' * n})

*-right-zero : {m : Int} -> m * zero-int == zero-int
*-right-zero {zero-int} = refl
*-right-zero {pos zero} = refl
*-right-zero {neg zero} = refl
*-right-zero {pos (suc m')} = *-right-zero {pos m'}
*-right-zero {neg (suc m')} = *-right-zero {neg m'}

private
  *-right-one' : (m : Nat) -> (nonneg m) * (int 1) == (nonneg m)
  *-right-one' zero = refl
  *-right-one' (suc m') = cong add1 (*-right-one' m')

*-right-one : {m : Int} -> m * (int 1) == m
*-right-one {nonneg m} = *-right-one' m
*-right-one {neg m} = cong minus (*-right-one' (suc m))

*-left-one : {m : Int} -> (int 1) * m == m
*-left-one = +-right-zero

private
  *-right-negative-one' : (m : Nat) -> (nonneg (suc m)) * (neg zero) == (neg m)
  *-right-negative-one' zero = refl
  *-right-negative-one' (suc m') = cong sub1 (*-right-negative-one' m')

*-right-negative-one : {m : Int} -> m * (neg zero) == - m
*-right-negative-one {zero-int} = refl
*-right-negative-one {pos m'} = (*-right-negative-one' m')
*-right-negative-one {neg m'} = cong minus (*-right-negative-one' m')


add1-extract-* : {m n : Int} -> add1 m * n == n + m * n
add1-extract-* {zero-int} = refl
add1-extract-* {pos m'} = refl
add1-extract-* {neg zero} {n} =
  begin
    add1 (neg zero) * n
  ==<>
    zero-int
  ==< sym (add-minus-zero {n}) >
    n + - n
  ==< (+-right {n} (cong minus (sym (+-right-zero {n})))) >
    n + - (n + zero-int)
  ==<>
    n + (neg zero) * n
  end
add1-extract-* {neg (suc m')} {n} =
  begin
    add1 (neg (suc m')) * n
  ==<>
    neg m' * n
  ==<>
    - (pos m' * n)
  ==<>
    (zero-int) + - ((pos m') * n)
  ==< +-left (sym (add-minus-zero {n})) >
    (n + - n) + - ((pos m') * n)
  ==< +-assoc {n} >
    n + (- n + - ((pos m') * n))
  ==< +-right {n} (sym (minus-distrib-+ {n})) >
    n + (- (n + (pos m') * n))
  ==<>
    n + (neg (suc m')) * n
  end

private
  add1-extract-*-right' : (m : Nat) (n : Int) -> (nonneg m) * add1 n == (nonneg m) + (nonneg m) * n
  add1-extract-*-right' zero n = refl
  add1-extract-*-right' (suc m') n =
    begin
      nonneg (suc m') * add1 n
    ==<>
      add1 n + nonneg m' * add1 n
    ==< +-right {add1 n} (add1-extract-*-right' m' n) >
      add1 n + (nonneg m' + nonneg m' * n)
    ==< sym (+-assoc {add1 n}) >
      (add1 n + nonneg m') + nonneg m' * n
    ==< +-left (add1-extract-left {n}) >
      add1 (n + nonneg m') + nonneg m' * n
    ==< +-left (cong add1 (+-commute {n})) >
      add1 (nonneg m' + n) + nonneg m' * n
    ==< +-left (sym (add1-extract-left {nonneg m'} {n})) >
      (add1 (nonneg m') + n) + nonneg m' * n
    ==< +-assoc {add1 (nonneg m')} >
      nonneg (suc m') + nonneg (suc m') * n
    end


add1-extract-*-right : {m n : Int} -> m * add1 n == m + m * n
add1-extract-*-right {nonneg m} {n} = add1-extract-*-right' m n
add1-extract-*-right {neg m'} {n} =
  begin
    neg m' * add1 n
  ==<>
    - (pos m' * add1 n)
  ==< cong minus (add1-extract-*-right' (suc m') n) >
    - (pos m' + pos m' * n)
  ==< minus-distrib-+ {pos m'} >
    neg m' + neg m' * n
  end


sub1-extract-* : {m n : Int} -> sub1 m * n == - n + m * n
sub1-extract-* {zero-int} {n} =
  begin
    sub1 zero-int * n
  ==<>
    - (n + zero-int)
  ==< cong minus (+-right-zero) >
    - n
  ==< sym +-right-zero >
    - n + zero-int * n
  end
sub1-extract-* {pos zero} {n} =
  begin
    sub1 (pos zero) * n
  ==<>
    zero-int
  ==< sym (add-minus-zero {n}) >
    n + - n
  ==< +-commute {n} >
    - n + n
  ==< +-right { - n} (sym (+-right-zero {n})) >
    - n + (n + zero-int)
  ==<>
    - n + (pos zero) * n
  end
sub1-extract-* {pos (suc m')} {n} =
  begin
    sub1 (pos (suc m')) * n
  ==<>
    (pos m') * n
  ==< +-left (sym (add-minus-zero {n})) >
    (n + - n) + (pos m') * n
  ==< +-left (+-commute {n}) >
    (- n + n) + (pos m') * n
  ==< +-assoc { - n} >
    - n + (n + (pos m') * n)
  ==<>
    - n + (pos (suc m')) * n
  end
sub1-extract-* {neg m'} {n} =
  begin
    sub1 (neg m') * n
  ==<>
    - (add1 (pos m') * n)
  ==< cong minus (add1-extract-* {pos m'} {n}) >
    - (n + (pos m') * n)
  ==< minus-distrib-+ {n} >
    - n + (neg m') * n
  end


sub1-extract-*-right : {m n : Int} -> m * sub1 n == - m + m * n
sub1-extract-*-right {zero-int} = refl
sub1-extract-*-right {pos zero} {n} =
  begin
    (pos zero) * (sub1 n)
  ==< +-right-zero {sub1 n} >
    (sub1 n)
  ==< cong sub1 (sym (+-right-zero {n})) >
    (sub1 (n + zero-int))
  ==<>
    - (pos zero) + (pos zero) * n
  end
sub1-extract-*-right {neg zero} {n} =
  begin
    (neg zero) * (sub1 n)
  ==< cong minus (+-right-zero {sub1 n}) >
    - (sub1 n)
  ==< sym (add1-minus->minus-sub1 {n}) >
    add1 (- n)
  ==< cong add1 (cong minus (sym (+-right-zero {n}))) >
    add1 (- (n + zero-int))
  ==<>
    - (neg zero) + (neg zero) * n
  end
sub1-extract-*-right {pos (suc m')} {n} =
  begin
    (pos (suc m')) * (sub1 n)
  ==<>
    sub1 n + pos m' * sub1 n
  ==< +-right {sub1 n} (sub1-extract-*-right {pos m'} {n}) >
    sub1 n + (- pos m' + pos m' * n)
  ==< sym (+-assoc {sub1 n}) >
    (sub1 n + - pos m') + (pos m') * n
  ==< +-left (sub1-extract-left {n}) >
    sub1 (n + - pos m') + (pos m') * n
  ==< +-left (cong sub1 (+-commute {n})) >
    sub1 (- pos m' + n) + (pos m') * n
  ==< +-left (sym (sub1-extract-left { - pos m'})) >
    (sub1 (- pos m') + n) + (pos m') * n
  ==< +-assoc {sub1 (- pos m')} >
    sub1 (- pos m') + (n + (pos m') * n)
  ==<>
    - (pos (suc m')) + (pos (suc m')) * n
  end
sub1-extract-*-right {neg (suc m')} {n} =
  begin
    (neg (suc m')) * (sub1 n)
  ==<>
    - (sub1 n + pos m' * sub1 n)
  ==< minus-distrib-+ {sub1 n} >
    - sub1 n + neg m' * sub1 n
  ==< +-right { - sub1 n} (sub1-extract-*-right {neg m'} {n}) >
    - sub1 n + (- neg m' + neg m' * n)
  ==< sym (+-assoc { - sub1 n}) >
    (- sub1 n + - neg m') + neg m' * n
  ==< +-left (sym (minus-distrib-+ {sub1 n})) >
    - (sub1 n + neg m') + neg m' * n
  ==< +-left (cong minus (sub1-extract-left {n})) >
    - sub1 (n + neg m') + neg m' * n
  ==< +-left (cong minus (cong sub1 (+-commute {n}))) >
    - sub1 (neg m' + n) + neg m' * n
  ==< +-left (cong minus (sym (sub1-extract-left {neg m'}))) >
    - (sub1 (neg m') + n) + neg m' * n
  ==< +-left (minus-distrib-+ {sub1 (neg m')}) >
    (- sub1 (neg m') + - n) + neg m' * n
  ==< +-assoc { - sub1 (neg m')} >
    - sub1 (neg m') + (- n + neg m' * n)
  ==< +-right { - sub1 (neg m')} (sym (minus-distrib-+ {n})) >
    - (neg (suc m')) + (neg (suc m')) * n
  end


*-distrib-+ : {m n p : Int} -> (m + n) * p == (m * p) + (n * p)
*-distrib-+ {zero-int} = refl
*-distrib-+ {pos zero} {n} {p} =
  begin
    (pos zero + n) * p
  ==<>
    (add1 n) * p
  ==< add1-extract-* {n} >
    p + (n * p)
  ==< +-left (sym (+-right-zero {p}))  >
    (p + zero-int) + (n * p)
  ==<>
    (pos zero * p) + (n * p)
  end
*-distrib-+ {neg zero} {n} {p} =
  begin
    (neg zero + n) * p
  ==<>
    (sub1 n) * p
  ==< sub1-extract-* {n} >
    - p + (n * p)
  ==< +-left (cong minus (sym (+-right-zero {p}))) >
    - (p + zero-int) + (n * p)
  ==<>
    (neg zero * p) + (n * p)
  end
*-distrib-+ {pos (suc m')} {n} {p} =
  begin
    (pos (suc m') + n) * p
  ==<>
    add1 (pos m' + n) * p
  ==< add1-extract-* {pos m' + n} >
    p + ((pos m') + n) * p
  ==< +-right {p} (*-distrib-+ {pos m'}) >
    p + ((pos m') * p + n * p)
  ==< sym (+-assoc {p}) >
    (p + (pos m') * p) + n * p
  ==<>
    (pos (suc m') * p) + (n * p)
  end
*-distrib-+ {neg (suc m')} {n} {p} =
  begin
    (neg (suc m') + n) * p
  ==<>
    sub1 (neg m' + n) * p
  ==< sub1-extract-* {neg m' + n} >
    - p + ((neg m') + n) * p
  ==< +-right { - p} (*-distrib-+ {neg m'}) >
    - p + ((neg m') * p + n * p)
  ==< sym (+-assoc { - p}) >
    (- p + (neg m') * p) + n * p
  ==< +-left (sym (minus-distrib-+ {p})) >
    - (p + (pos m') * p) + n * p
  ==<>
    (neg (suc m') * p) + (n * p)
  end


private
  *-assoc' : (m : Nat) (n o : Int) -> ((nonneg m) * n) * o == (nonneg m) * (n * o)
  *-assoc' zero _ _ = refl
  *-assoc' (suc m') n o =
    begin
      (nonneg (suc m') * n) * o
    ==<>
      (n + nonneg m' * n) * o
    ==< *-distrib-+ {n} >
      n * o + (nonneg m' * n) * o
    ==< +-right {n * o} (*-assoc' m' n o) >
      n * o + nonneg m' * (n * o)
    ==<>
      nonneg (suc m') * (n * o)
    end

*-assoc : {m n o : Int} -> (m * n) * o == m * (n * o)
*-assoc {nonneg m} {n} {o} =  *-assoc' m n o
*-assoc {neg m'} {n} {o} =
  begin
    (neg m' * n) * o
  ==< (*-left {o} (minus-extract-left {pos m'} {n})) >
    - (pos m' * n) * o
  ==< minus-extract-left {pos m' * n} >
    - ((pos m' * n) * o)
  ==< (cong minus (*-assoc' (suc m') n o)) >
    - (pos m' * (n * o))
  ==<>
    (neg m') * (n * o)
  end


*-commute : {m n : Int} -> m * n == n * m
*-commute {zero-int} {n} = sym (*-right-zero {n})
*-commute {pos zero} {n} =
  begin
    pos zero * n
  ==< +-right-zero {n} >
    n
  ==< sym *-right-one >
    n * pos zero
  end
*-commute {neg zero} {n} =
  begin
    neg zero * n
  ==< cong minus (+-right-zero {n}) >
    - n
  ==< sym (*-right-negative-one {n}) >
    n * neg zero
  end
*-commute {pos (suc m')} {n} =
  begin
    pos (suc m') * n
  ==<>
    n + pos m' * n
  ==< +-right {n} (*-commute {pos m'} {n}) >
    n + n * pos m'
  ==< sym (add1-extract-*-right {n}) >
    n * pos (suc m')
  end
*-commute {neg (suc m')} {n} =
  begin
    neg (suc m') * n
  ==<>
    - (n + pos m' * n)
  ==< minus-distrib-+ {n} >
    - n + neg m' * n
  ==< +-right { - n} (*-commute {neg m'} {n}) >
    - n + n * neg m'
  ==< sym (sub1-extract-*-right {n}) >
    n * neg (suc m')
  end

*-distrib-+-left : {m n p : Int} -> m * (n + p) == (m * n) + (m * p)
*-distrib-+-left {m} {n} {p} =
  *-commute {m} {n + p}
  >=> (*-distrib-+ {n} {p} {m})
  >=> (\i -> (*-commute {n} {m} i) + (*-commute {p} {m} i))

minus-extract-right : {m n : Int} -> m * - n == - (m * n)
minus-extract-right {m} {n} =
  (*-commute {m}) >=> (minus-extract-left {n}) >=> (cong minus (*-commute {n}))

minus-extract-both : {m n : Int} -> - m * - n == (m * n)
minus-extract-both {m} {n} =
  (minus-extract-right { - m} {n}) >=> (cong minus (minus-extract-left {m} {n}))
  >=> (minus-double-inverse {m * n})


*-Pos-Pos : {m n : Int} -> .(Pos m) -> .(Pos n) -> Pos (m * n)
*-Pos-Pos {pos zero} _ pr = +-Pos-NonNeg pr tt
*-Pos-Pos {pos (suc m)} _ pr = +-Pos-Pos pr (*-Pos-Pos {pos m} tt pr)

*-Pos-NonNeg : {m n : Int} -> .(Pos m) -> .(NonNeg n) -> NonNeg (m * n)
*-Pos-NonNeg {pos zero} _ pr = +-NonNeg-NonNeg pr tt
*-Pos-NonNeg {pos (suc m)} _ pr = +-NonNeg-NonNeg pr (*-Pos-NonNeg {pos m} tt pr)

*-NonNeg-Pos : {m n : Int} -> .(NonNeg m) -> .(Pos n) -> NonNeg (m * n)
*-NonNeg-Pos {m} {n} nn p = transport (cong NonNeg (*-commute {n} {m})) (*-Pos-NonNeg p nn)

*-Neg-NonNeg : {m n : Int} -> .(Neg m) -> .(NonNeg n) -> NonPos (m * n)
*-Neg-NonNeg {neg m} {n} _ pn = minus-NonNeg (*-Pos-NonNeg {pos m} _ pn)

*-NonNeg-Neg : {m n : Int} -> .(NonNeg m) -> .(Neg n) -> NonPos (m * n)
*-NonNeg-Neg {m} {n} nn neg-n = transport (cong NonPos (*-commute {n} {m})) (*-Neg-NonNeg neg-n nn)

*-Pos-NonPos : {m n : Int} -> .(Pos m) -> .(NonPos n) -> NonPos (m * n)
*-Pos-NonPos {pos zero} _ pr = +-NonPos-NonPos pr tt
*-Pos-NonPos {pos (suc m)} _ pr = +-NonPos-NonPos pr (*-Pos-NonPos {pos m} tt pr)

*-NonPos-Pos : {m n : Int} -> .(NonPos m) -> .(Pos n) -> NonPos (m * n)
*-NonPos-Pos {m} {n} np p = transport (cong NonPos (*-commute {n} {m})) (*-Pos-NonPos p np)

*-Neg-NonPos : {m n : Int} -> .(Neg m) -> .(NonPos n) -> NonNeg (m * n)
*-Neg-NonPos {neg m} {n} neg-m np = minus-NonPos (*-Pos-NonPos {pos m} _ np)

*-NonPos-Neg : {m n : Int} -> .(NonPos m) -> .(Neg n) -> NonNeg (m * n)
*-NonPos-Neg {m} {n} np neg-n = transport (cong NonNeg (*-commute {n} {m})) (*-Neg-NonPos neg-n np)

*-Pos-Neg : {m n : Int} -> .(Pos m) -> .(Neg n) -> Neg (m * n)
*-Pos-Neg {pos zero} _ pr = +-Neg-NonPos pr tt
*-Pos-Neg {pos (suc m)} _ pr = +-Neg-Neg pr (*-Pos-Neg {pos m} tt pr)

*-Neg-Pos : {m n : Int} -> .(Neg m) -> .(Pos n) -> Neg (m * n)
*-Neg-Pos {m} {n} p1 p2 = subst Neg (*-commute {n} {m}) (*-Pos-Neg p2 p1)

*-NonNeg-NonNeg : {m n : Int} -> .(NonNeg m) -> .(NonNeg n) -> NonNeg (m * n)
*-NonNeg-NonNeg {zero-int} _ pr = tt
*-NonNeg-NonNeg {pos zero} _ pr = +-NonNeg-NonNeg pr tt
*-NonNeg-NonNeg {pos (suc m)} _ pr = +-NonNeg-NonNeg pr (*-Pos-NonNeg {pos m} tt pr)

*-Neg-Neg : {m n : Int} -> .(Neg m) -> .(Neg n) -> Pos (m * n)
*-Neg-Neg {neg m} {neg n} p1 p2 = subst Pos proof (*-Pos-Pos {pos m} {pos n} tt tt)
  where
  proof : (pos m) * (pos n) == (neg m) * (neg n)
  proof = (minus-extract-left {neg m} {pos n})
          >=> (cong minus (minus-extract-right {neg m} {neg n}))
          >=> (minus-double-inverse {neg m * neg n})

*-NonZero-NonZero : {m n : Int} -> .(NonZero m) -> .(NonZero n) -> NonZero (m * n)
*-NonZero-NonZero m@{pos _} n@{pos _} p1 p2 = Pos->NonZero (*-Pos-Pos {m} {n} p1 p2)
*-NonZero-NonZero m@{pos _} n@{neg _} p1 p2 = Neg->NonZero (*-Pos-Neg {m} {n} p1 p2)
*-NonZero-NonZero m@{neg _} n@{pos _} p1 p2 = Neg->NonZero (*-Neg-Pos {m} {n} p1 p2)
*-NonZero-NonZero m@{neg _} n@{neg _} p1 p2 = Pos->NonZero (*-Neg-Neg {m} {n} p1 p2)


add1-disjoint : (m : Int) -> add1 m != m
add1-disjoint zero-int      p = transport (\i -> Pos (p i)) tt
add1-disjoint (neg zero)    p = transport (\i -> Zero (p i)) tt
add1-disjoint (pos zero)    p = add1-disjoint zero-int (cong sub1 p)
add1-disjoint (pos (suc x)) p = add1-disjoint (pos x)  (cong sub1 p)
add1-disjoint (neg (suc x)) p = add1-disjoint (neg x)  (cong add1 p)

sub1-disjoint : (m : Int) -> sub1 m != m
sub1-disjoint zero-int      p = transport (\i -> Neg (p i)) tt
sub1-disjoint (pos zero)    p = transport (\i -> Zero (p i)) tt
sub1-disjoint (neg zero)    p = sub1-disjoint zero-int (cong add1 p)
sub1-disjoint (neg (suc x)) p = sub1-disjoint (neg x)  (cong add1 p)
sub1-disjoint (pos (suc x)) p = sub1-disjoint (pos x)  (cong sub1 p)

zero!=non-zero : {x y : Int} {z-x : Zero x} {nz-y : NonZero y} -> x == y -> Bot
zero!=non-zero {zero-int} {nz-y = nz} p = transport (\i -> NonZero (p (~ i))) nz
zero!=non-zero {pos _}    {z-x = z}   _ = z
zero!=non-zero {neg _}    {z-x = z}   _ = z


+-right-id : {m n : Int} -> m + n == m -> n == (int 0)
+-right-id {zero-int} {_} pr = pr
+-right-id {pos zero} {n} pr = +-right-id {zero-int} {n} (sym sub1-add1-id >=> (cong sub1 pr))
+-right-id {pos (suc m)} {n} pr = +-right-id {pos m} {n} (sym sub1-add1-id >=> (cong sub1 pr))
+-right-id {neg zero} {n} pr = +-right-id {zero-int} {n} (sym add1-sub1-id >=> (cong add1 pr))
+-right-id {neg (suc m)} {n} pr = +-right-id {neg m} {n} (sym add1-sub1-id >=> (cong add1 pr))

+-left-id : {m n : Int} -> m + n == n -> m == (int 0)
+-left-id {m} {n} pr = +-right-id (sym (+-commute {m} {n}) >=> pr)

*-left-zero-eq : {m n : Int} -> (NonZero n) -> m * n == (int 0) -> m == (int 0)
*-left-zero-eq {zero-int} {_} _ _ = refl
*-left-zero-eq {pos m} {pos n} _ pr =
  bot-elim (subst Pos pr (*-Pos-Pos {pos m} {pos n} tt tt))
*-left-zero-eq {pos m} {neg n} _ pr =
  bot-elim (subst Neg pr (*-Pos-Neg {pos m} {neg n} tt tt))
*-left-zero-eq {neg m} {pos n} _ pr =
  bot-elim (subst Neg pr (*-Neg-Pos {neg m} {pos n} tt tt))
*-left-zero-eq {neg m} {neg n} _ pr =
  bot-elim (subst Pos pr (*-Neg-Neg {neg m} {neg n} tt tt))

*-right-zero-eq : {m n : Int} -> (NonZero m) -> m * n == (int 0) -> n == (int 0)
*-right-zero-eq {_} {zero-int} _ _ = refl
*-right-zero-eq {pos m} {pos n} _ pr =
  bot-elim (subst Pos pr (*-Pos-Pos {pos m} {pos n} tt tt))
*-right-zero-eq {pos m} {neg n} _ pr =
  bot-elim (subst Neg pr (*-Pos-Neg {pos m} {neg n} tt tt))
*-right-zero-eq {neg m} {pos n} _ pr =
  bot-elim (subst Neg pr (*-Neg-Pos {neg m} {pos n} tt tt))
*-right-zero-eq {neg m} {neg n} _ pr =
  bot-elim (subst Pos pr (*-Neg-Neg {neg m} {neg n} tt tt))

*-left-id : {m n : Int} -> (NonZero n) -> m * n == n -> m == (int 1)
*-left-id {zero-int} {pos _} tt p = bot-elim (zero!=non-zero p)
*-left-id {zero-int} {neg _} tt p = bot-elim (zero!=non-zero p)
*-left-id {pos zero} {_} _ _ = refl
*-left-id {pos (suc m)} {pos n} nz pr =
  bot-elim (subst Pos (+-right-id pr) (*-Pos-Pos {pos m} {pos n} tt tt))
*-left-id {pos (suc m)} {neg n} _ pr =
  bot-elim (subst Neg (+-right-id pr) (*-Pos-Neg {pos m} {neg n} tt tt))
*-left-id {neg m} {pos n} _ pr =
  bot-elim (subst Neg pr (*-Neg-Pos {neg m} {pos n} tt tt))
*-left-id {neg m} {neg n} _ pr =
  bot-elim (subst Pos pr (*-Neg-Neg {neg m} {neg n} tt tt))

*-right-id : {m n : Int} -> (NonZero m) -> m * n == m -> n == (int 1)
*-right-id {m} {n} nz pr = *-left-id nz (sym (*-commute {m} {n}) >=> pr)

private
  *nz-right-injective : {m n : Nat} {p : Int} -> .(NonZero p) -> (m *nz p) == (n *nz p) -> m == n
  *nz-right-injective {m = zero}  {n = zero}         p-nz path = refl
  *nz-right-injective {m = suc m} {n = zero}  {p = p} p-nz path =
    bot-elim (transport (cong NonZero path) (*-NonZero-NonZero {pos m} {p} tt p-nz))
  *nz-right-injective {m = zero}  {n = suc n} {p = p} p-nz path =
    bot-elim (transport (cong NonZero (sym path)) (*-NonZero-NonZero {pos n} {p} tt p-nz))
  *nz-right-injective {m = suc m} {n = suc n} {p = p} p-nz path =
    cong suc (*nz-right-injective p-nz (+-left-injective p path))


*-right-injective : {m n p : Int} .(nz : (NonZero n)) -> (m * n) == (p * n) -> m == p
*-right-injective {nonneg m} {n} {nonneg p} nz path = cong nonneg (*nz-right-injective nz path)
*-right-injective {neg m}    {n} {neg p}    nz path =
 cong (\x -> (- (int x))) (*nz-right-injective nz (minus-injective path))
*-right-injective m@{nonneg _} n@{pos _} p@{neg _} nz path =
  bot-elim (NonNeg->¬Neg pn-nonneg pn-neg)
  where
  pn-nonneg : NonNeg (p * n)
  pn-nonneg = transport (cong NonNeg path) (*-NonNeg-Pos {m} {n} _ _)

  pn-neg : Neg (p * n)
  pn-neg = *-Neg-Pos {p} {n} _ _
*-right-injective m@{nonneg _} n@{neg _} p@{neg _}    nz path =
  bot-elim (NonPos->¬Pos pn-nonpos pn-pos)
  where
  pn-nonpos : NonPos (p * n)
  pn-nonpos = transport (cong NonPos path) (*-NonNeg-Neg {m} {n} _ _)

  pn-pos : Pos (p * n)
  pn-pos = *-Neg-Neg {p} {n} _ _
*-right-injective m@{neg _} n@{pos _} p@{nonneg _} nz path =
  bot-elim (NonNeg->¬Neg pn-nonneg pn-neg)
  where
  pn-neg : Neg (p * n)
  pn-neg = transport (cong Neg path) (*-Neg-Pos {m} {n} _ _)

  pn-nonneg : NonNeg (p * n)
  pn-nonneg = *-NonNeg-Pos {p} {n} _ _
*-right-injective m@{neg _} n@{neg _} p@{nonneg _} nz path =
  bot-elim (NonPos->¬Pos pn-nonpos pn-pos)
  where
  pn-pos : Pos (p * n)
  pn-pos = transport (cong Pos path) (*-Neg-Neg {m} {n} _ _)

  pn-nonpos : NonPos (p * n)
  pn-nonpos = *-NonNeg-Neg {p} {n} _ _

*-left-injective : {m n p : Int} .(nz : (NonZero m)) -> (m * n) == (m * p) -> n == p
*-left-injective {m} {n} {p} nz path =
  *-right-injective nz (*-commute {n} {m} >=> path >=> *-commute {m} {p})


_^_ : Int -> Nat -> Int
a ^ zero = (int 1)
a ^ (suc b) = a * a ^ b

^-right-one : {a : Int} -> a ^ 1 == a
^-right-one = *-right-one

nonneg-injective : {m n : Nat} -> nonneg m == nonneg n -> m == n
nonneg-injective {zero}  {zero}  p = refl
nonneg-injective {suc _} {zero}  p = bot-elim (zero!=non-zero (sym p))
nonneg-injective {zero}  {suc _} p = bot-elim (zero!=non-zero p)
nonneg-injective {suc _} {suc _} p = cong suc (nonneg-injective (cong sub1 p))

neg-injective : {m n : Nat} -> neg m == neg n -> m == n
neg-injective {zero}  {zero}  p = refl
neg-injective {suc _} {zero}  p = bot-elim (zero!=non-zero (sym (cong add1 p)))
neg-injective {zero}  {suc _} p = bot-elim (zero!=non-zero (cong add1 p))
neg-injective {suc _} {suc _} p = cong suc (neg-injective (cong add1 p))

nonneg-neg-absurd : {m n : Nat} -> nonneg m == neg n -> Bot
nonneg-neg-absurd p = transport (\i -> NonNeg (p i)) tt


decide-int : (x : Int) -> (y : Int) -> Dec (x == y)
decide-int (nonneg m) (nonneg n) with decide-nat m n
... | (yes p) = yes (cong nonneg p)
... | (no f) = no (\ pr -> f (nonneg-injective pr))
decide-int (neg m) (neg n) with decide-nat m n
... | (yes p) = yes (cong neg p)
... | (no f) = no (\ pr -> f (neg-injective pr))
decide-int m@(nonneg _) n@(neg _) = no nonneg-neg-absurd
decide-int m@(neg _) n@(nonneg _) = no (\ p -> nonneg-neg-absurd (sym p))


discreteInt : Discrete Int
discreteInt = decide-int

isSetInt : isSet Int
isSetInt = Discrete->isSet discreteInt


IntMonoid+ : Monoid Int
IntMonoid+ = record {
  ε = (int 0);
  _∙_ = _+_;
  ∙-assoc = \ {m} {n} {o} -> +-assoc {m} {n} {o};
  ∙-left-ε = +-left-zero;
  ∙-right-ε = +-right-zero }

IntMonoid* : Monoid Int
IntMonoid* = record {
  ε = (int 1);
  _∙_ = _*_;
  ∙-assoc = \ {m} {n} {o} -> *-assoc {m} {n} {o};
  ∙-left-ε = *-left-one;
  ∙-right-ε = *-right-one }
