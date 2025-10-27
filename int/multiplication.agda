{-# OPTIONS --cubical --safe --exact-split #-}

module int.multiplication where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import int.add1
open import int.addition
open import int.base

open EqReasoning

private
  _*nz_ : Nat -> Int -> Int
  zero *nz m = zero-int
  suc n *nz m = m +ᵉ (n *nz m)

infixl 7 _*ᵉ_
_*ᵉ_ : Int -> Int -> Int
nonneg m *ᵉ n = m *nz n
neg m *ᵉ n = -(suc m *nz n)


opaque
  _ℤ*_ : Int -> Int -> Int
  _ℤ*_ = _*ᵉ_

private
  infixl 7 _*_
  _*_ : Int -> Int -> Int
  _*_ = _ℤ*_

opaque
  unfolding _ℤ*_

  ℤ*-eval : {m n : Int} -> m * n == m *ᵉ n
  ℤ*-eval = refl

  ℤ*-right : {m n p : Int} -> (n == p) -> m * n == m * p
  ℤ*-right {m} id = cong (\x -> m * x) id

  ℤ*-left : {m n p : Int} -> (n == p) -> n * m == p * m
  ℤ*-left {m} id = cong (\x -> x * m) id

  private
    *-right : {m n p : Int} -> (n == p) -> m * n == m * p
    *-right {m} = ℤ*-right {m}
    *-left : {m n p : Int} -> (n == p) -> n * m == p * m
    *-left = ℤ*-left

  ℤminus-extract-left : {m n : Int} -> - m * n == - (m * n)
  ℤminus-extract-left {zero-int} = refl
  ℤminus-extract-left {pos m'} = refl
  ℤminus-extract-left {neg m'} {n} = sym (minus-double-inverse)

  ℤ*-left-zero : {m : Int} -> zero-int * m == zero-int
  ℤ*-left-zero = refl

  opaque
    unfolding _ℤ+_

    ℤ*-right-zero : {m : Int} -> m * zero-int == zero-int
    ℤ*-right-zero {zero-int} = refl
    ℤ*-right-zero {pos zero} = refl
    ℤ*-right-zero {neg zero} = refl
    ℤ*-right-zero {pos (suc m')} = ℤ*-right-zero {pos m'}
    ℤ*-right-zero {neg (suc m')} = ℤ*-right-zero {neg m'}

  private
    opaque
      unfolding _ℤ+_
      *-right-one' : (m : Nat) -> (nonneg m) * (int 1) == (nonneg m)
      *-right-one' zero = refl
      *-right-one' (suc m') = cong add1 (*-right-one' m')

  ℤ*-right-one : {m : Int} -> m * (int 1) == m
  ℤ*-right-one {nonneg m} = *-right-one' m
  ℤ*-right-one {neg m} = cong -_ (*-right-one' (suc m))

  ℤ*-left-one : {m : Int} -> (int 1) * m == m
  ℤ*-left-one = sym ℤ+-eval >=> +-right-zero

  private
    *-left-zero : {m : Int} -> zero-int * m == zero-int
    *-left-zero {m} = ℤ*-left-zero {m}
    *-right-zero : {m : Int} -> m * zero-int == zero-int
    *-right-zero {m} = ℤ*-right-zero {m}
    *-right-one : {m : Int} -> m * (int 1) == m
    *-right-one = ℤ*-right-one

  private
    opaque
      unfolding _ℤ+_
      *-right-negative-one' : (m : Nat) -> (nonneg (suc m)) * (neg zero) == (neg m)
      *-right-negative-one' zero = refl
      *-right-negative-one' (suc m') = cong sub1 (*-right-negative-one' m')

  *-right-negative-one : {m : Int} -> m * (neg zero) == - m
  *-right-negative-one {zero-int} = refl
  *-right-negative-one {pos m'} = (*-right-negative-one' m')
  *-right-negative-one {neg m'} = cong -_ (*-right-negative-one' m')

  add1-extract-* : {m n : Int} -> add1 m * n == n + m * n
  add1-extract-* {zero-int} = sym ℤ+-eval
  add1-extract-* {pos m'} = sym ℤ+-eval
  add1-extract-* {neg zero} {n} =
    begin
      add1 (neg zero) * n
    ==<>
      zero-int
    ==< sym +-inverse >
      n + - n
    ==< (+-right (cong -_ (sym (+-right-zero)))) >
      n + - (n + zero-int)
    ==< +-right (cong -_ ℤ+-eval) >
      n + (neg zero) * n
    end
  add1-extract-* {neg (suc m')} {n} =
    begin
      add1 (neg (suc m')) * n
    ==<>
      neg m' * n
    ==<>
      - (pos m' * n)
    ==< sym ℤ+-eval >
      (zero-int) + - ((pos m') * n)
    ==< +-left (sym +-inverse) >
      (n + - n) + - ((pos m') * n)
    ==< +-assoc >
      n + (- n + - ((pos m') * n))
    ==< +-right (sym minus-distrib-plus) >
      n + (- (n + (pos m') * n))
    ==< +-right (cong -_ ℤ+-eval) >
      n + (neg (suc m')) * n
    end

  private
    add1-extract-*-right' : (m : Nat) (n : Int) -> (nonneg m) * add1 n == (nonneg m) + (nonneg m) * n
    add1-extract-*-right' zero n = sym ℤ+-eval
    add1-extract-*-right' (suc m') n =
      begin
        nonneg (suc m') * add1 n
      ==< sym ℤ+-eval >
        add1 n + nonneg m' * add1 n
      ==< +-right (add1-extract-*-right' m' n) >
        add1 n + (nonneg m' + nonneg m' * n)
      ==< sym +-assoc >
        (add1 n + nonneg m') + nonneg m' * n
      ==< +-left (add1-extract-left {n}) >
        add1 (n + nonneg m') + nonneg m' * n
      ==< +-left (cong add1 (+-commute)) >
        add1 (nonneg m' + n) + nonneg m' * n
      ==< +-left (sym (add1-extract-left {nonneg m'} {n})) >
        (add1 (nonneg m') + n) + nonneg m' * n
      ==< +-assoc >
       _
      ==< +-right ℤ+-eval >
        nonneg (suc m') + nonneg (suc m') * n
      end



  add1-extract-*-right : {m n : Int} -> m * add1 n == m + m * n
  add1-extract-*-right {nonneg m} {n} = add1-extract-*-right' m n
  add1-extract-*-right {neg m'} {n} =
    begin
      neg m' * add1 n
    ==<>
      - (pos m' * add1 n)
    ==< cong -_ (add1-extract-*-right' (suc m') n) >
      - (pos m' + pos m' * n)
    ==< minus-distrib-plus >
      neg m' + neg m' * n
    end


sub1-extract-* : {m n : Int} -> sub1 m * n == - n + m * n
sub1-extract-* =
  sym minus-double-inverse >=>
  cong -_ (sym ℤminus-extract-left >=>
           ℤ*-left (sym add1-minus->minus-sub1) >=>
           add1-extract-*) >=>
  minus-distrib-plus >=>
  +-right (cong -_ ℤminus-extract-left >=> minus-double-inverse)


opaque
  unfolding _ℤ*_

  sub1-extract-*-right : {m n : Int} -> m * sub1 n == - m + m * n
  sub1-extract-*-right {zero-int} = sym +-left-zero
  sub1-extract-*-right {pos zero} {n} =
    begin
      (pos zero) * (sub1 n)
    ==< sym ℤ+-eval >=> +-right-zero >
      (sub1 n)
    ==< cong sub1 (sym +-right-zero) >
      (sub1 (n + zero-int))
    ==< sym ℤ+-eval >=> +-right ℤ+-eval >
      - (pos zero) + (pos zero) * n
    end
  sub1-extract-*-right {neg zero} {n} =
    begin
      (neg zero) * (sub1 n)
    ==< cong -_ (sym ℤ+-eval >=> +-right-zero) >
      - (sub1 n)
    ==< sym (add1-minus->minus-sub1 {n}) >
      add1 (- n)
    ==< cong add1 (cong -_ (sym +-right-zero)) >
      add1 (- (n + zero-int))
    ==< sym ℤ+-eval >
      (pos zero) + (- (n + zero-int))
    ==< +-right (cong -_ ℤ+-eval) >
      (pos zero) + (neg zero) * n
    ==<>
      - (neg zero) + (neg zero) * n
    end
  sub1-extract-*-right {pos (suc m')} {n} =
    begin
      (pos (suc m')) * (sub1 n)
    ==< sym ℤ+-eval >
      sub1 n + pos m' * sub1 n
    ==< +-right (sub1-extract-*-right {pos m'} {n}) >
      sub1 n + (- pos m' + pos m' * n)
    ==< sym +-assoc >
      (sub1 n + - pos m') + (pos m') * n
    ==< +-left (sub1-extract-left {n}) >
      sub1 (n + - pos m') + (pos m') * n
    ==< +-left (cong sub1 +-commute) >
      sub1 (- pos m' + n) + (pos m') * n
    ==< +-left (sym (sub1-extract-left { - pos m'})) >
      (sub1 (- pos m') + n) + (pos m') * n
    ==< +-assoc >
      sub1 (- pos m') + (n + (pos m') * n)
    ==< +-right ℤ+-eval >
      - (pos (suc m')) + (pos (suc m')) * n
    end
  sub1-extract-*-right {neg (suc m')} {n} =
    begin
      (neg (suc m')) * (sub1 n)
    ==< cong -_ (sym ℤ+-eval) >
      - (sub1 n + pos m' * sub1 n)
    ==< minus-distrib-plus >
      - sub1 n + neg m' * sub1 n
    ==< +-right (sub1-extract-*-right {neg m'} {n}) >
      - sub1 n + (- neg m' + neg m' * n)
    ==< sym +-assoc >
      (- sub1 n + - neg m') + neg m' * n
    ==< +-left (sym minus-distrib-plus) >
      - (sub1 n + neg m') + neg m' * n
    ==< +-left (cong -_ (sub1-extract-left {n})) >
      - sub1 (n + neg m') + neg m' * n
    ==< +-left (cong -_ (cong sub1 +-commute)) >
      - sub1 (neg m' + n) + neg m' * n
    ==< +-left (cong -_ (sym (sub1-extract-left {neg m'}))) >
      - (sub1 (neg m') + n) + neg m' * n
    ==< +-left minus-distrib-plus >
      (- sub1 (neg m') + - n) + neg m' * n
    ==< +-assoc >
      - sub1 (neg m') + (- n + neg m' * n)
    ==< +-right (sym minus-distrib-plus >=> cong -_ ℤ+-eval) >
      - (neg (suc m')) + (neg (suc m')) * n
    end


  ℤ*-distrib-+-right : {m n p : Int} -> (m + n) * p == (m * p) + (n * p)
  ℤ*-distrib-+-right {zero-int} = *-left +-left-zero >=> sym +-left-zero
  ℤ*-distrib-+-right {pos zero} {n} {p} =
    begin
      (pos zero + n) * p
    ==< *-left ℤ+-eval >
      (add1 n) * p
    ==< add1-extract-* {n} >
      p + (n * p)
    ==< +-left (sym +-right-zero)  >
      (p + zero-int) + (n * p)
    ==< +-left ℤ+-eval >
      (pos zero * p) + (n * p)
    end
  ℤ*-distrib-+-right {neg zero} {n} {p} =
    begin
      (neg zero + n) * p
    ==< *-left ℤ+-eval >
      (sub1 n) * p
    ==< sub1-extract-* {n} >
      - p + (n * p)
    ==< +-left (cong -_ (sym +-right-zero)) >
      - (p + zero-int) + (n * p)
    ==< +-left (cong -_ ℤ+-eval) >
      (neg zero * p) + (n * p)
    end
  ℤ*-distrib-+-right {pos (suc m')} {n} {p} =
    begin
      (pos (suc m') + n) * p
    ==< *-left add1-extract-left >
      add1 (pos m' + n) * p
    ==< add1-extract-* {pos m' + n} >
      p + ((pos m') + n) * p
    ==< +-right (ℤ*-distrib-+-right {pos m'}) >
      p + ((pos m') * p + n * p)
    ==< sym +-assoc >
      (p + (pos m') * p) + n * p
    ==< +-left ℤ+-eval >
      (pos (suc m') * p) + (n * p)
    end
  ℤ*-distrib-+-right {neg (suc m')} {n} {p} =
    begin
      (neg (suc m') + n) * p
    ==< *-left sub1-extract-left >
      sub1 (neg m' + n) * p
    ==< sub1-extract-* {neg m' + n} >
      - p + ((neg m') + n) * p
    ==< +-right (ℤ*-distrib-+-right {neg m'}) >
      - p + ((neg m') * p + n * p)
    ==< sym +-assoc >
      (- p + (neg m') * p) + n * p
    ==< +-left (sym minus-distrib-plus) >
      - (p + (pos m') * p) + n * p
    ==< +-left (cong -_ ℤ+-eval) >
      (neg (suc m') * p) + (n * p)
    end



  private
    *-assoc' : (m : Nat) (n o : Int) -> ((nonneg m) * n) * o == (nonneg m) * (n * o)
    *-assoc' zero _ _ = refl
    *-assoc' (suc m') n o =
      begin
        (nonneg (suc m') * n) * o
      ==< *-left (sym ℤ+-eval) >
        (n + nonneg m' * n) * o
      ==< ℤ*-distrib-+-right {n} >
        n * o + (nonneg m' * n) * o
      ==< +-right (*-assoc' m' n o) >
        n * o + nonneg m' * (n * o)
      ==< ℤ+-eval >
        nonneg (suc m') * (n * o)
      end


  ℤ*-assoc : {m n o : Int} -> (m * n) * o == m * (n * o)
  ℤ*-assoc {nonneg m} {n} {o} =  *-assoc' m n o
  ℤ*-assoc {neg m'} {n} {o} =
    begin
      (neg m' * n) * o
    ==< (*-left {o} (ℤminus-extract-left {pos m'} {n})) >
      - (pos m' * n) * o
    ==< ℤminus-extract-left {pos m' * n} >
      - ((pos m' * n) * o)
    ==< (cong -_ (*-assoc' (suc m') n o)) >
      - (pos m' * (n * o))
    ==<>
      (neg m') * (n * o)
    end


  ℤ*-commute : {m n : Int} -> m * n == n * m
  ℤ*-commute {zero-int} {n} = sym (*-right-zero {n})
  ℤ*-commute {pos zero} {n} =
    begin
      pos zero * n
    ==< sym ℤ+-eval >=> +-right-zero >
      n
    ==< sym *-right-one >
      n * pos zero
    end
  ℤ*-commute {neg zero} {n} =
    begin
      neg zero * n
    ==<  cong -_ (sym ℤ+-eval >=> +-right-zero) >
      - n
    ==< sym (*-right-negative-one {n}) >
      n * neg zero
    end
  ℤ*-commute {pos (suc m')} {n} =
    begin
      pos (suc m') * n
    ==< sym ℤ+-eval >
      n + pos m' * n
    ==< +-right (ℤ*-commute {pos m'} {n}) >
      n + n * pos m'
    ==< sym (add1-extract-*-right {n}) >
      n * pos (suc m')
    end
  ℤ*-commute {neg (suc m')} {n} =
    begin
      neg (suc m') * n
    ==< cong -_ (sym ℤ+-eval) >
      - (n + pos m' * n)
    ==< minus-distrib-plus >
      - n + neg m' * n
    ==< +-right (ℤ*-commute {neg m'} {n}) >
      - n + n * neg m'
    ==< sym (sub1-extract-*-right {n}) >
      n * neg (suc m')
    end
  private
    *-commute : {m n : Int} -> m * n == n * m
    *-commute {m} {n} = ℤ*-commute {m} {n}
    *-assoc : {m n o : Int} -> (m * n) * o == m * (n * o)
    *-assoc {m} {n} {o} = ℤ*-assoc {m} {n} {o}


  ℤ*-distrib-+-left : {m n p : Int} -> m * (n + p) == (m * n) + (m * p)
  ℤ*-distrib-+-left {m} {n} {p} =
    *-commute {m} {n + p}
    >=> (ℤ*-distrib-+-right {n} {p} {m})
    >=> (\i -> (*-commute {n} {m} i) + (*-commute {p} {m} i))

  ℤminus-extract-right : {m n : Int} -> m * - n == - (m * n)
  ℤminus-extract-right {m} {n} =
    (*-commute {m}) >=> (ℤminus-extract-left {n}) >=> (cong -_ (*-commute {n}))

  ℤminus-extract-both : {m n : Int} -> - m * - n == (m * n)
  ℤminus-extract-both {m} {n} =
    (ℤminus-extract-right { - m} {n}) >=>
    (cong -_ (ℤminus-extract-left {m} {n})) >=>
    minus-double-inverse


opaque
  _^_ : Int -> Nat -> Int
  a ^ zero = (int 1)
  a ^ (suc b) = a * a ^ b

  ^-right-zero : {a : Int} -> a ^ 0 == (int 1)
  ^-right-zero = refl

  ^-right-suc : {a : Int} {n : Nat} -> a ^ (suc n) == a * (a ^ n)
  ^-right-suc = refl

  ^-right-one : {a : Int} -> a ^ 1 == a
  ^-right-one = *-right-one
