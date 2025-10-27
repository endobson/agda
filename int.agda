{-# OPTIONS --cubical --safe --exact-split #-}

module int where

open import base
open import discrete
open import equality
open import hlevel
open import int.add1
open import int.addition
open import monoid
open import nat
open import nat.order
open import order
open import order.instances.nat
open import relation
open import sign using (Sign ; s⁻¹_ ; _s*_ ; pos-sign ; zero-sign ; neg-sign )

open import int.base public
open import int.cover public
open import int.sign public

open EqReasoning

private
  infix 9 -_
  -_ : Int -> Int
  -_ = ℤ-_

abstract
  ℤminus-double-inverse : {x : Int} -> - - x == x
  ℤminus-double-inverse {zero-int} = refl
  ℤminus-double-inverse {pos x'} = refl
  ℤminus-double-inverse {neg x'} = refl

  minus-injective : {x y : Int} -> - x == - y -> x == y
  minus-injective p = sym ℤminus-double-inverse >=> cong (-_) p >=> ℤminus-double-inverse

private
  infixl 6 _+_
  _+_ : Int -> Int -> Int
  _+_ = _ℤ+_

opaque
  unfolding _ℤ+_

  private
    +-right : {m n p : Int} -> (n == p) -> m + n == m + p
    +-right {m} = ℤ+-right {m}
    +-left : {m n p : Int} -> (n == p) -> n + m == p + m
    +-left = ℤ+-left

  ℤ+-assoc : {m n o : Int} -> (m + n) + o == m + (n + o)
  ℤ+-assoc {zero-int} = refl
  ℤ+-assoc {pos zero} {n} {o} = add1-extract-left {n} {o}
  ℤ+-assoc {neg zero} {n} {o} = sub1-extract-left {n} {o}
  ℤ+-assoc {pos (suc m')} {n} {o} =
    begin
      (pos (suc m') + n) + o
    ==<>
      (add1 (pos m') + n) + o
    ==< +-left (add1-extract-left {pos m'}) >
      (add1 (pos m' + n)) + o
    ==< add1-extract-left {pos m' + n} >
      add1 ((pos m' + n) + o)
    ==< cong add1 (ℤ+-assoc {pos m'}) >
      add1 (pos m' + (n + o))
    ==<>
      pos (suc m') + (n + o)
    end
  ℤ+-assoc {neg (suc m')} {n} {o} =
    begin
      (neg (suc m') + n) + o
    ==<>
      (sub1 (neg m') + n) + o
    ==< +-left (sub1-extract-left {neg m'}) >
      (sub1 (neg m' + n)) + o
    ==< sub1-extract-left {neg m' + n} >
      sub1 ((neg m' + n) + o)
    ==< cong sub1 (ℤ+-assoc {neg m'}) >
      sub1 (neg m' + (n + o))
    ==<>
      neg (suc m') + (n + o)
    end

  private
    +-assoc : {m n o : Int} -> (m + n) + o == m + (n + o)
    +-assoc {m} {n} {o} = ℤ+-assoc {m} {n} {o}

  ℤ+-commute : {m n : Int} -> (m + n) == (n + m)
  ℤ+-commute {nonneg zero} {n} = sym (ℤ+-right-zero n)
  ℤ+-commute {neg zero} {n} =
   begin
     neg zero + n
   ==<>
     sub1 n
   ==< cong sub1 (sym (ℤ+-right-zero n)) >
     sub1 (n + zero-int)
   ==< sym (sub1-extract-right {n}) >
     n + sub1 zero-int
   ==<>
     n + neg zero
   end
  ℤ+-commute {nonneg (suc m')} {n} =
    begin
      nonneg (suc m') + n
    ==<>
      add1 (nonneg m' + n)
    ==< cong add1 (ℤ+-commute {nonneg m'}) >
      add1 (n + nonneg m')
    ==< sym (add1-extract-right {n})>
      n + add1 (nonneg m')
    ==<>
      n + nonneg (suc m')
    end
  ℤ+-commute {neg (suc m')} {n} =
    begin
      neg (suc m') + n
    ==<>
      sub1 (neg m' + n)
    ==< cong sub1 (ℤ+-commute {neg m'}) >
      sub1 (n + neg m')
    ==< sym (sub1-extract-right {n})>
      n + sub1 (neg m')
    ==<>
      n + neg (suc m')
    end

  private
    +-commute : {m n : Int} -> (m + n) == (n + m)
    +-commute {m} {n} = ℤ+-commute {m} {n}

  add1-NonNeg : {n : Int} -> (NonNeg n) -> (Pos (add1 n))
  add1-NonNeg {nonneg _} _ = tt
  add1-NonNeg {neg _} (inj-l ())
  add1-NonNeg {neg _} (inj-r ())

  add1-Pos : {n : Int} -> .(Pos n) -> (Pos (add1 n))
  add1-Pos {pos _} _ = tt

  sub1-NonPos : {n : Int} -> (NonPos n) -> (Neg (sub1 n))
  sub1-NonPos {zero-int} _ = tt
  sub1-NonPos {neg _} _ = tt
  sub1-NonPos {pos _} (inj-l ())
  sub1-NonPos {pos _} (inj-r ())

  sub1-Neg : {n : Int} -> .(Neg n) -> (Neg (sub1 n))
  sub1-Neg {neg _} _ = tt


  +-Pos-NonNeg : {m n : Int} -> (Pos m) -> (NonNeg n) -> Pos (m + n)
  +-Pos-NonNeg {pos zero} _ p = add1-NonNeg p
  +-Pos-NonNeg {pos (suc m)} _ p = add1-Pos (+-Pos-NonNeg {pos m} tt p)

  +-NonNeg-Pos : {m n : Int} -> (NonNeg m) -> (Pos n) -> Pos (m + n)
  +-NonNeg-Pos {m} {n} p1 p2 = subst Pos (+-commute {n} {m}) (+-Pos-NonNeg p2 p1)

  +-Pos-Pos : {m n : Int} -> (Pos m) -> (Pos n) -> Pos (m + n)
  +-Pos-Pos p1 p2 = +-Pos-NonNeg p1 (Pos->NonNeg p2)

  +-Neg-NonPos : {m n : Int} -> (Neg m) -> (NonPos n) -> Neg (m + n)
  +-Neg-NonPos {neg zero} _ p = sub1-NonPos p
  +-Neg-NonPos {neg (suc m)} _ p = sub1-Neg (+-Neg-NonPos {neg m} tt p)

  +-NonPos-Neg : {m n : Int} -> (NonPos m) -> (Neg n) -> Neg (m + n)
  +-NonPos-Neg {m} {n} p1 p2 = subst Neg (+-commute {n} {m}) (+-Neg-NonPos p2 p1)

  +-Neg-Neg : {m n : Int} -> (Neg m) -> (Neg n) -> Neg (m + n)
  +-Neg-Neg p1 p2 = +-Neg-NonPos p1 (Neg->NonPos p2)

  +-NonNeg-NonNeg : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> NonNeg (m + n)
  +-NonNeg-NonNeg {zero-int} {zero-int} p1 p2 = inj-r tt
  +-NonNeg-NonNeg {zero-int} {pos n} p1 p2 =
    Pos->NonNeg {zero-int + pos n} (+-NonNeg-Pos {zero-int} {pos n} (inj-r tt) tt)
  +-NonNeg-NonNeg {pos m} {zero-int} p1 p2 =
    Pos->NonNeg {pos m + zero-int} (+-Pos-NonNeg {pos m} {zero-int} tt (inj-r tt))
  +-NonNeg-NonNeg {pos m} {pos n} p1 p2 =
    Pos->NonNeg {pos m + pos n} (+-Pos-Pos {pos m} {pos n} tt tt)
  +-NonNeg-NonNeg {neg _} {_} (inj-l ())
  +-NonNeg-NonNeg {neg _} {_} (inj-r ())
  +-NonNeg-NonNeg {pos _} {neg _} _ (inj-l ())
  +-NonNeg-NonNeg {pos _} {neg _} _ (inj-r ())
  +-NonNeg-NonNeg {zero-int} {neg _} _ (inj-l ())
  +-NonNeg-NonNeg {zero-int} {neg _} _ (inj-r ())

  +-NonPos-NonPos : {m n : Int} -> (NonPos m) -> (NonPos n) -> NonPos (m + n)
  +-NonPos-NonPos {zero-int} {zero-int} p1 p2 = inj-r tt
  +-NonPos-NonPos {zero-int} {neg n} p1 p2 =
    Neg->NonPos {zero-int + neg n} (+-NonPos-Neg {zero-int} {neg n} (inj-r tt) tt)
  +-NonPos-NonPos {neg m} {zero-int} p1 p2 =
    Neg->NonPos {neg m + zero-int} (+-Neg-NonPos {neg m} {zero-int} tt (inj-r tt))
  +-NonPos-NonPos {neg m} {neg n} p1 p2 =
    Neg->NonPos {neg m + neg n} (+-Neg-Neg {neg m} {neg n} tt tt)
  +-NonPos-NonPos {pos _} {_} (inj-l ())
  +-NonPos-NonPos {pos _} {_} (inj-r ())
  +-NonPos-NonPos {neg _} {pos _} _ (inj-l ())
  +-NonPos-NonPos {neg _} {pos _} _ (inj-r ())
  +-NonPos-NonPos {zero-int} {pos _} _ (inj-l ())
  +-NonPos-NonPos {zero-int} {pos _} _ (inj-r ())

  minus-Pos : {n : Int} -> .(Pos n) -> Neg (- n)
  minus-Pos {pos _} _ = tt

  minus-Neg : {n : Int} -> .(Neg n) -> Pos (- n)
  minus-Neg {neg _} _ = tt

  minus-NonPos : {n : Int} -> (NonPos n) -> NonNeg (- n)
  minus-NonPos {zero-int} _ = inj-r tt
  minus-NonPos {neg _}    _ = inj-l tt
  minus-NonPos {pos _} (inj-l ())
  minus-NonPos {pos _} (inj-r ())

  minus-NonNeg : {n : Int} -> (NonNeg n) -> NonPos (- n)
  minus-NonNeg {zero-int} _ = inj-r tt
  minus-NonNeg {pos _}    _ = inj-l tt
  minus-NonNeg {neg _} (inj-l ())
  minus-NonNeg {neg _} (inj-r ())


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
    ==< +-right {pos n'} (cong -_ (sub1-add1-id)) >
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
    ==< +-right {neg n'} (cong -_ (add1-sub1-id {neg n'})) >
      neg n' + - neg n'
    ==< add-minus-zero {neg n'}  >
      zero-int
    end

  private
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
  unfolding _ℤ+_ _ℤ*_

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
  ℤminus-extract-left {neg m'} {n} = sym (ℤminus-double-inverse {pos m' * n})

  ℤ*-left-zero : {m : Int} -> zero-int * m == zero-int
  ℤ*-left-zero = refl

  ℤ*-right-zero : {m : Int} -> m * zero-int == zero-int
  ℤ*-right-zero {zero-int} = refl
  ℤ*-right-zero {pos zero} = refl
  ℤ*-right-zero {neg zero} = refl
  ℤ*-right-zero {pos (suc m')} = ℤ*-right-zero {pos m'}
  ℤ*-right-zero {neg (suc m')} = ℤ*-right-zero {neg m'}

  private
    *-right-one' : (m : Nat) -> (nonneg m) * (int 1) == (nonneg m)
    *-right-one' zero = refl
    *-right-one' (suc m') = cong add1 (*-right-one' m')

  ℤ*-right-one : {m : Int} -> m * (int 1) == m
  ℤ*-right-one {nonneg m} = *-right-one' m
  ℤ*-right-one {neg m} = cong -_ (*-right-one' (suc m))

  ℤ*-left-one : {m : Int} -> (int 1) * m == m
  ℤ*-left-one = ℤ+-right-zero _

  private
    *-left-zero : {m : Int} -> zero-int * m == zero-int
    *-left-zero {m} = ℤ*-left-zero {m}
    *-right-zero : {m : Int} -> m * zero-int == zero-int
    *-right-zero {m} = ℤ*-right-zero {m}
    *-right-one : {m : Int} -> m * (int 1) == m
    *-right-one = ℤ*-right-one

  private
    *-right-negative-one' : (m : Nat) -> (nonneg (suc m)) * (neg zero) == (neg m)
    *-right-negative-one' zero = refl
    *-right-negative-one' (suc m') = cong sub1 (*-right-negative-one' m')

  *-right-negative-one : {m : Int} -> m * (neg zero) == - m
  *-right-negative-one {zero-int} = refl
  *-right-negative-one {pos m'} = (*-right-negative-one' m')
  *-right-negative-one {neg m'} = cong -_ (*-right-negative-one' m')


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
    ==< (+-right {n} (cong -_ (sym (ℤ+-right-zero n)))) >
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
    ==< cong -_ (add1-extract-*-right' (suc m') n) >
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
    ==< cong -_ (ℤ+-right-zero _) >
      - n
    ==< sym (ℤ+-right-zero _) >
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
    ==< +-right { - n} (sym (ℤ+-right-zero n)) >
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
    ==< cong -_ (add1-extract-* {pos m'} {n}) >
      - (n + (pos m') * n)
    ==< minus-distrib-+ {n} >
      - n + (neg m') * n
    end


  sub1-extract-*-right : {m n : Int} -> m * sub1 n == - m + m * n
  sub1-extract-*-right {zero-int} = refl
  sub1-extract-*-right {pos zero} {n} =
    begin
      (pos zero) * (sub1 n)
    ==< ℤ+-right-zero (sub1 n) >
      (sub1 n)
    ==< cong sub1 (sym (ℤ+-right-zero n)) >
      (sub1 (n + zero-int))
    ==<>
      - (pos zero) + (pos zero) * n
    end
  sub1-extract-*-right {neg zero} {n} =
    begin
      (neg zero) * (sub1 n)
    ==< cong -_ (ℤ+-right-zero (sub1 n)) >
      - (sub1 n)
    ==< sym (add1-minus->minus-sub1 {n}) >
      add1 (- n)
    ==< cong add1 (cong -_ (sym (ℤ+-right-zero n))) >
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
    ==< +-left (cong -_ (sub1-extract-left {n})) >
      - sub1 (n + neg m') + neg m' * n
    ==< +-left (cong -_ (cong sub1 (+-commute {n}))) >
      - sub1 (neg m' + n) + neg m' * n
    ==< +-left (cong -_ (sym (sub1-extract-left {neg m'}))) >
      - (sub1 (neg m') + n) + neg m' * n
    ==< +-left (minus-distrib-+ {sub1 (neg m')}) >
      (- sub1 (neg m') + - n) + neg m' * n
    ==< +-assoc { - sub1 (neg m')} >
      - sub1 (neg m') + (- n + neg m' * n)
    ==< +-right { - sub1 (neg m')} (sym (minus-distrib-+ {n})) >
      - (neg (suc m')) + (neg (suc m')) * n
    end


  ℤ*-distrib-+-right : {m n p : Int} -> (m + n) * p == (m * p) + (n * p)
  ℤ*-distrib-+-right {zero-int} = refl
  ℤ*-distrib-+-right {pos zero} {n} {p} =
    begin
      (pos zero + n) * p
    ==<>
      (add1 n) * p
    ==< add1-extract-* {n} >
      p + (n * p)
    ==< +-left (sym (ℤ+-right-zero p))  >
      (p + zero-int) + (n * p)
    ==<>
      (pos zero * p) + (n * p)
    end
  ℤ*-distrib-+-right {neg zero} {n} {p} =
    begin
      (neg zero + n) * p
    ==<>
      (sub1 n) * p
    ==< sub1-extract-* {n} >
      - p + (n * p)
    ==< +-left (cong -_ (sym (ℤ+-right-zero p))) >
      - (p + zero-int) + (n * p)
    ==<>
      (neg zero * p) + (n * p)
    end
  ℤ*-distrib-+-right {pos (suc m')} {n} {p} =
    begin
      (pos (suc m') + n) * p
    ==<>
      add1 (pos m' + n) * p
    ==< add1-extract-* {pos m' + n} >
      p + ((pos m') + n) * p
    ==< +-right {p} (ℤ*-distrib-+-right {pos m'}) >
      p + ((pos m') * p + n * p)
    ==< sym (+-assoc {p}) >
      (p + (pos m') * p) + n * p
    ==<>
      (pos (suc m') * p) + (n * p)
    end
  ℤ*-distrib-+-right {neg (suc m')} {n} {p} =
    begin
      (neg (suc m') + n) * p
    ==<>
      sub1 (neg m' + n) * p
    ==< sub1-extract-* {neg m' + n} >
      - p + ((neg m') + n) * p
    ==< +-right { - p} (ℤ*-distrib-+-right {neg m'}) >
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
      ==< ℤ*-distrib-+-right {n} >
        n * o + (nonneg m' * n) * o
      ==< +-right {n * o} (*-assoc' m' n o) >
        n * o + nonneg m' * (n * o)
      ==<>
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
    ==< ℤ+-right-zero n >
      n
    ==< sym *-right-one >
      n * pos zero
    end
  ℤ*-commute {neg zero} {n} =
    begin
      neg zero * n
    ==< cong -_ (ℤ+-right-zero n) >
      - n
    ==< sym (*-right-negative-one {n}) >
      n * neg zero
    end
  ℤ*-commute {pos (suc m')} {n} =
    begin
      pos (suc m') * n
    ==<>
      n + pos m' * n
    ==< +-right {n} (ℤ*-commute {pos m'} {n}) >
      n + n * pos m'
    ==< sym (add1-extract-*-right {n}) >
      n * pos (suc m')
    end
  ℤ*-commute {neg (suc m')} {n} =
    begin
      neg (suc m') * n
    ==<>
      - (n + pos m' * n)
    ==< minus-distrib-+ {n} >
      - n + neg m' * n
    ==< +-right { - n} (ℤ*-commute {neg m'} {n}) >
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
    (ℤminus-extract-right { - m} {n}) >=> (cong -_ (ℤminus-extract-left {m} {n}))
    >=> (ℤminus-double-inverse {m * n})

  minus-isSign : {m : Int} {s : Sign} -> isSign s m -> isSign (s⁻¹ s) (- m)
  minus-isSign {zero-int} {zero-sign} _ = tt
  minus-isSign {pos _} {pos-sign} _ = tt
  minus-isSign {neg _} {neg-sign} _ = tt


  Recomputable-Pos : Recomputable Pos
  Recomputable-Pos {pos x} _ = tt

  -- Recomputable-NonZero : Recomputable NonZero
  -- Recomputable-NonZero {pos x} _ = inj-l tt
  -- Recomputable-NonZero {neg x} _ = inj-r tt

  *-Pos-Pos : {m n : Int} -> (Pos m) -> (Pos n) -> Pos (m * n)
  *-Pos-Pos {pos zero} _ pr = +-Pos-NonNeg pr (inj-r tt)
  *-Pos-Pos {pos (suc m)} _ pr = +-Pos-Pos pr (*-Pos-Pos {pos m} tt pr)

  *-Pos-NonNeg : {m n : Int} -> (Pos m) -> (NonNeg n) -> NonNeg (m * n)
  *-Pos-NonNeg {pos zero} _ pr = +-NonNeg-NonNeg pr (inj-r tt)
  *-Pos-NonNeg {pos (suc m)} _ pr = +-NonNeg-NonNeg pr (*-Pos-NonNeg {pos m} tt pr)

  *-NonNeg-Pos : {m n : Int} -> (NonNeg m) -> (Pos n) -> NonNeg (m * n)
  *-NonNeg-Pos {m} {n} nn p = transport (cong NonNeg (*-commute {n} {m})) (*-Pos-NonNeg p nn)

  *-Neg-NonNeg : {m n : Int} -> (Neg m) -> (NonNeg n) -> NonPos (m * n)
  *-Neg-NonNeg {neg m} {n} _ pn = minus-NonNeg (*-Pos-NonNeg {pos m} _ pn)

  *-NonNeg-Neg : {m n : Int} -> (NonNeg m) -> (Neg n) -> NonPos (m * n)
  *-NonNeg-Neg {m} {n} nn neg-n = transport (cong NonPos (*-commute {n} {m})) (*-Neg-NonNeg neg-n nn)

  *-Pos-NonPos : {m n : Int} -> (Pos m) -> (NonPos n) -> NonPos (m * n)
  *-Pos-NonPos {pos zero} _ pr = +-NonPos-NonPos pr (inj-r tt)
  *-Pos-NonPos {pos (suc m)} _ pr = +-NonPos-NonPos pr (*-Pos-NonPos {pos m} tt pr)

  *-NonPos-Pos : {m n : Int} -> (NonPos m) -> (Pos n) -> NonPos (m * n)
  *-NonPos-Pos {m} {n} np p = transport (cong NonPos (*-commute {n} {m})) (*-Pos-NonPos p np)

  *-Neg-NonPos : {m n : Int} -> (Neg m) -> (NonPos n) -> NonNeg (m * n)
  *-Neg-NonPos {neg m} {n} neg-m np = minus-NonPos (*-Pos-NonPos {pos m} _ np)

  *-NonPos-Neg : {m n : Int} -> (NonPos m) -> (Neg n) -> NonNeg (m * n)
  *-NonPos-Neg {m} {n} np neg-n = transport (cong NonNeg (*-commute {n} {m})) (*-Neg-NonPos neg-n np)

  *-NonNeg-NonPos : {m n : Int} -> (NonNeg m) -> (NonPos n) -> NonPos (m * n)
  *-NonNeg-NonPos {zero-int} {n} _ np = subst NonPos (sym (*-left-zero {n})) (inj-r tt)
  *-NonNeg-NonPos {pos m} {n} nn np = *-Pos-NonPos {pos m} _ np
  *-NonNeg-NonPos {neg m} {n} (inj-l ())
  *-NonNeg-NonPos {neg m} {n} (inj-r ())

  *-NonPos-NonNeg : {m n : Int} -> (NonPos m) -> (NonNeg n) -> NonPos (m * n)
  *-NonPos-NonNeg {m} {n} np nn = subst NonPos (*-commute {n} {m}) (*-NonNeg-NonPos {n} {m} nn np)

  *-Pos-Neg : {m n : Int} -> (Pos m) -> (Neg n) -> Neg (m * n)
  *-Pos-Neg {pos zero} _ pr = +-Neg-NonPos pr (inj-r tt)
  *-Pos-Neg {pos (suc m)} _ pr = +-Neg-Neg pr (*-Pos-Neg {pos m} tt pr)

  *-Neg-Pos : {m n : Int} -> (Neg m) -> (Pos n) -> Neg (m * n)
  *-Neg-Pos {m} {n} p1 p2 = subst Neg (*-commute {n} {m}) (*-Pos-Neg p2 p1)

  *-NonNeg-NonNeg : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> NonNeg (m * n)
  *-NonNeg-NonNeg {zero-int} _ pr = (inj-r tt)
  *-NonNeg-NonNeg {pos zero} _ pr = +-NonNeg-NonNeg pr (inj-r tt)
  *-NonNeg-NonNeg {pos (suc m)} _ pr = +-NonNeg-NonNeg pr (*-Pos-NonNeg {pos m} tt pr)
  *-NonNeg-NonNeg {neg m} (inj-l ())
  *-NonNeg-NonNeg {neg m} (inj-r ())

  *-Neg-Neg : {m n : Int} -> (Neg m) -> (Neg n) -> Pos (m * n)
  *-Neg-Neg {neg m} {neg n} p1 p2 = subst Pos proof (*-Pos-Pos {pos m} {pos n} tt tt)
    where
    proof : (pos m) * (pos n) == (neg m) * (neg n)
    proof = (ℤminus-extract-left {neg m} {pos n})
            >=> (cong -_ (ℤminus-extract-right {neg m} {neg n}))
            >=> (ℤminus-double-inverse {neg m * neg n})

  *-NonZero-NonZero : {m n : Int} -> (NonZero m) -> (NonZero n) -> NonZero (m * n)
  *-NonZero-NonZero {m} {n} (inj-l p1) (inj-l p2) = Pos->NonZero (*-Pos-Pos {m} {n} p1 p2)
  *-NonZero-NonZero {m} {n} (inj-l p1) (inj-r p2) = Neg->NonZero (*-Pos-Neg {m} {n} p1 p2)
  *-NonZero-NonZero {m} {n} (inj-r p1) (inj-l p2) = Neg->NonZero (*-Neg-Pos {m} {n} p1 p2)
  *-NonZero-NonZero {m} {n} (inj-r p1) (inj-r p2) = Pos->NonZero (*-Neg-Neg {m} {n} p1 p2)

  *-Zero₁ : {m n : Int} -> Zero m -> Zero (m * n)
  *-Zero₁ {zero-int} {n} _ = subst Zero (sym (*-left-zero {n})) tt
  *-Zero₂ : {m n : Int} -> Zero n -> Zero (m * n)
  *-Zero₂ {m} {zero-int} _ = subst Zero (sym (*-right-zero {m})) tt

  *-NonZero₁ : {m n : Int} -> NonZero (m * n) -> NonZero m
  *-NonZero₁ m@{pos _} n@{pos _}    _  = inj-l tt
  *-NonZero₁ m@{pos _} n@{neg _}    _  = inj-l tt
  *-NonZero₁ m@{pos _} n@{zero-int} (inj-l pn)  = bot-elim (subst Pos (*-right-zero {m}) pn)
  *-NonZero₁ m@{pos _} n@{zero-int} (inj-r nn)  = bot-elim (subst Neg (*-right-zero {m}) nn)
  *-NonZero₁ m@{neg _} n@{pos _}       _ = inj-r tt
  *-NonZero₁ m@{neg _} n@{neg _}       _ = inj-r tt
  *-NonZero₁ m@{neg _} n@{zero-int} (inj-l pn)  = bot-elim (subst Pos (*-right-zero {m}) pn)
  *-NonZero₁ m@{neg _} n@{zero-int} (inj-r nn)  = bot-elim (subst Neg (*-right-zero {m}) nn)
  *-NonZero₁ m@{zero-int} {n} (inj-l pn)  = bot-elim (subst Pos (*-left-zero {n}) pn)
  *-NonZero₁ m@{zero-int} {n} (inj-r nn)  = bot-elim (subst Neg (*-left-zero {n}) nn)

  *-isSign : {s1 s2 : Sign} {m n : Int} -> isSign s1 m -> isSign s2 n -> isSign (s1 s* s2) (m * n)
  *-isSign {pos-sign}  {pos-sign}          i1 i2 = *-Pos-Pos i1 i2
  *-isSign {pos-sign}  {zero-sign} {m = m} i1 i2 = *-Zero₂ {m = m} i2
  *-isSign {pos-sign}  {neg-sign}          i1 i2 = *-Pos-Neg i1 i2
  *-isSign {zero-sign} {pos-sign}          i1 i2 = *-Zero₁ i1
  *-isSign {zero-sign} {zero-sign}         i1 i2 = *-Zero₁ i1
  *-isSign {zero-sign} {neg-sign}          i1 i2 = *-Zero₁ i1
  *-isSign {neg-sign}  {pos-sign}          i1 i2 = *-Neg-Pos i1 i2
  *-isSign {neg-sign}  {zero-sign} {m = m} i1 i2 = *-Zero₂ {m = m} i2
  *-isSign {neg-sign}  {neg-sign}          i1 i2 = *-Neg-Neg i1 i2

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

  zero!=non-zero : {x y : Int} (z-x : Zero x) (nz-y : NonZero y) -> x == y -> Bot
  zero!=non-zero z-x nz-y p = NonZero->¬Zero nz-y (subst Zero p z-x)

  NonZero->!=0 : {x : Int} (nz-x : NonZero x) -> x != (int 0)
  NonZero->!=0 nz x=0 = zero!=non-zero tt nz (sym x=0)

  int->sign-preserves-* : {m n : Int} -> int->sign (m * n) == (int->sign m) s* (int->sign n)
  int->sign-preserves-* {m} {n} =
    isSign-unique (isSign-self (m * n))
      (*-isSign {int->sign m} {int->sign n} (isSign-self m) (isSign-self n))

  _^_ : Int -> Nat -> Int
  a ^ zero = (int 1)
  a ^ (suc b) = a * a ^ b

  ^-right-zero : {a : Int} -> a ^ 0 == (int 1)
  ^-right-zero = refl

  ^-right-suc : {a : Int} {n : Nat} -> a ^ (suc n) == a * (a ^ n)
  ^-right-suc = refl

  ^-right-one : {a : Int} -> a ^ 1 == a
  ^-right-one = *-right-one

-- Nat arithmetic -> Integer arithmetic

ℕ->ℤ-minus : {m n : Nat} -> m < n -> ℕ->ℤ (n -' m) == (ℕ->ℤ n) + (- (ℕ->ℤ m))
ℕ->ℤ-minus {zero}  lt = sym (ℤ+-right-zero _)
ℕ->ℤ-minus {suc _} {zero} lt = bot-elim (zero-≮ lt)
ℕ->ℤ-minus {suc m} {suc n} lt =
  ℕ->ℤ-minus (pred-≤ lt) >=>
  sub1-extract-left >=>
  sym sub1-extract-right >=>
  +-right sub1-minus->minus-add1

ℕ->ℤ-+ : {m n : Nat} -> int (m +' n) == int m + int n
ℕ->ℤ-+ {zero} = sym (ℤ+-left-zero _)
ℕ->ℤ-+ {suc m} = cong add1 ℕ->ℤ-+ >=> sym add1-extract-left

ℕ->ℤ-* : {m n : Nat} -> int (m *' n) == int m * int n
ℕ->ℤ-* {zero} = sym *-left-zero
ℕ->ℤ-* {suc m} = ℕ->ℤ-+ >=> +-right ℕ->ℤ-* >=> sym add1-extract-*
