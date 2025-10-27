{-# OPTIONS --cubical --safe --exact-split #-}

module int where

open import additive-group.instances.int
open import additive-group
open import base
open import discrete
open import equality
open import hlevel
open import int.add1
open import int.addition
open import int.multiplication
open import monoid
open import nat
open import nat.order
open import order
open import order.instances.nat
open import relation
open import ring.implementations.int
open import semiring
open import sign using (Sign ; s⁻¹_ ; _s*_ ; pos-sign ; zero-sign ; neg-sign )

open import int.base public
open import int.cover public
open import int.sign public

open EqReasoning

opaque
  unfolding _ℤ+_

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
  +-NonNeg-Pos {m} {n} p1 p2 = subst Pos (+-commuteᵉ n m) (+-Pos-NonNeg p2 p1)

  +-Pos-Pos : {m n : Int} -> (Pos m) -> (Pos n) -> Pos (m + n)
  +-Pos-Pos p1 p2 = +-Pos-NonNeg p1 (Pos->NonNeg p2)

  +-Neg-NonPos : {m n : Int} -> (Neg m) -> (NonPos n) -> Neg (m + n)
  +-Neg-NonPos {neg zero} _ p = sub1-NonPos p
  +-Neg-NonPos {neg (suc m)} _ p = sub1-Neg (+-Neg-NonPos {neg m} tt p)

  +-NonPos-Neg : {m n : Int} -> (NonPos m) -> (Neg n) -> Neg (m + n)
  +-NonPos-Neg {m} {n} p1 p2 = subst Neg (+-commuteᵉ n m) (+-Neg-NonPos p2 p1)

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

  minus-isSign : {m : Int} {s : Sign} -> isSign s m -> isSign (s⁻¹ s) (- m)
  minus-isSign {zero-int} {zero-sign} _ = tt
  minus-isSign {pos _} {pos-sign} _ = tt
  minus-isSign {neg _} {neg-sign} _ = tt


  Recomputable-Pos : Recomputable Pos
  Recomputable-Pos {pos x} _ = tt

  -- Recomputable-NonZero : Recomputable NonZero
  -- Recomputable-NonZero {pos x} _ = inj-l tt
  -- Recomputable-NonZero {neg x} _ = inj-r tt

  opaque
    unfolding _ℤ+_ _ℤ*_

    *-Pos-Pos : {m n : Int} -> (Pos m) -> (Pos n) -> Pos (m * n)
    *-Pos-Pos {pos zero} _ pr = +-Pos-NonNeg pr (inj-r tt)
    *-Pos-Pos {pos (suc m)} _ pr = +-Pos-Pos pr (*-Pos-Pos {pos m} tt pr)

    *-Pos-NonNeg : {m n : Int} -> (Pos m) -> (NonNeg n) -> NonNeg (m * n)
    *-Pos-NonNeg {pos zero} _ pr = +-NonNeg-NonNeg pr (inj-r tt)
    *-Pos-NonNeg {pos (suc m)} _ pr = +-NonNeg-NonNeg pr (*-Pos-NonNeg {pos m} tt pr)

    *-NonNeg-Pos : {m n : Int} -> (NonNeg m) -> (Pos n) -> NonNeg (m * n)
    *-NonNeg-Pos {m} {n} nn p = transport (cong NonNeg (*-commuteᵉ n m)) (*-Pos-NonNeg p nn)

    *-Neg-NonNeg : {m n : Int} -> (Neg m) -> (NonNeg n) -> NonPos (m * n)
    *-Neg-NonNeg {neg m} {n} _ pn = minus-NonNeg (*-Pos-NonNeg {pos m} _ pn)

    *-NonNeg-Neg : {m n : Int} -> (NonNeg m) -> (Neg n) -> NonPos (m * n)
    *-NonNeg-Neg {m} {n} nn neg-n = transport (cong NonPos (*-commuteᵉ n m)) (*-Neg-NonNeg neg-n nn)

    *-Pos-NonPos : {m n : Int} -> (Pos m) -> (NonPos n) -> NonPos (m * n)
    *-Pos-NonPos {pos zero} _ pr = +-NonPos-NonPos pr (inj-r tt)
    *-Pos-NonPos {pos (suc m)} _ pr = +-NonPos-NonPos pr (*-Pos-NonPos {pos m} tt pr)

    *-NonPos-Pos : {m n : Int} -> (NonPos m) -> (Pos n) -> NonPos (m * n)
    *-NonPos-Pos {m} {n} np p = transport (cong NonPos (*-commuteᵉ n m)) (*-Pos-NonPos p np)

    *-Neg-NonPos : {m n : Int} -> (Neg m) -> (NonPos n) -> NonNeg (m * n)
    *-Neg-NonPos {neg m} {n} neg-m np = minus-NonPos (*-Pos-NonPos {pos m} _ np)

    *-NonPos-Neg : {m n : Int} -> (NonPos m) -> (Neg n) -> NonNeg (m * n)
    *-NonPos-Neg {m} {n} np neg-n = transport (cong NonNeg (*-commuteᵉ n m)) (*-Neg-NonPos neg-n np)

    *-NonNeg-NonPos : {m n : Int} -> (NonNeg m) -> (NonPos n) -> NonPos (m * n)
    *-NonNeg-NonPos {zero-int} {n} _ np = subst NonPos (sym (*-left-zeroᵉ n)) (inj-r tt)
    *-NonNeg-NonPos {pos m} {n} nn np = *-Pos-NonPos {pos m} _ np
    *-NonNeg-NonPos {neg m} {n} (inj-l ())
    *-NonNeg-NonPos {neg m} {n} (inj-r ())

    *-NonPos-NonNeg : {m n : Int} -> (NonPos m) -> (NonNeg n) -> NonPos (m * n)
    *-NonPos-NonNeg {m} {n} np nn = subst NonPos (*-commuteᵉ n m) (*-NonNeg-NonPos {n} {m} nn np)

    *-Pos-Neg : {m n : Int} -> (Pos m) -> (Neg n) -> Neg (m * n)
    *-Pos-Neg {pos zero} _ pr = +-Neg-NonPos pr (inj-r tt)
    *-Pos-Neg {pos (suc m)} _ pr = +-Neg-Neg pr (*-Pos-Neg {pos m} tt pr)

    *-Neg-Pos : {m n : Int} -> (Neg m) -> (Pos n) -> Neg (m * n)
    *-Neg-Pos {m} {n} p1 p2 = subst Neg (*-commuteᵉ n m) (*-Pos-Neg p2 p1)

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
      proof = (ℤminus-extract-left {neg m} {pos n}) >=>
              (cong -_ (ℤminus-extract-right {neg m} {neg n})) >=>
              minus-double-inverse

    *-NonZero-NonZero : {m n : Int} -> (NonZero m) -> (NonZero n) -> NonZero (m * n)
    *-NonZero-NonZero {m} {n} (inj-l p1) (inj-l p2) = Pos->NonZero (*-Pos-Pos {m} {n} p1 p2)
    *-NonZero-NonZero {m} {n} (inj-l p1) (inj-r p2) = Neg->NonZero (*-Pos-Neg {m} {n} p1 p2)
    *-NonZero-NonZero {m} {n} (inj-r p1) (inj-l p2) = Neg->NonZero (*-Neg-Pos {m} {n} p1 p2)
    *-NonZero-NonZero {m} {n} (inj-r p1) (inj-r p2) = Pos->NonZero (*-Neg-Neg {m} {n} p1 p2)

    *-Zero₁ : {m n : Int} -> Zero m -> Zero (m * n)
    *-Zero₁ {zero-int} {n} _ = subst Zero (sym (*-left-zeroᵉ n)) tt
    *-Zero₂ : {m n : Int} -> Zero n -> Zero (m * n)
    *-Zero₂ {m} {zero-int} _ = subst Zero (sym (*-right-zeroᵉ m)) tt

    *-NonZero₁ : {m n : Int} -> NonZero (m * n) -> NonZero m
    *-NonZero₁ m@{pos _} n@{pos _}    _  = inj-l tt
    *-NonZero₁ m@{pos _} n@{neg _}    _  = inj-l tt
    *-NonZero₁ m@{pos _} n@{zero-int} (inj-l pn)  = bot-elim (subst Pos (*-right-zeroᵉ m) pn)
    *-NonZero₁ m@{pos _} n@{zero-int} (inj-r nn)  = bot-elim (subst Neg (*-right-zeroᵉ m) nn)
    *-NonZero₁ m@{neg _} n@{pos _}       _ = inj-r tt
    *-NonZero₁ m@{neg _} n@{neg _}       _ = inj-r tt
    *-NonZero₁ m@{neg _} n@{zero-int} (inj-l pn)  = bot-elim (subst Pos (*-right-zeroᵉ m) pn)
    *-NonZero₁ m@{neg _} n@{zero-int} (inj-r nn)  = bot-elim (subst Neg (*-right-zeroᵉ m) nn)
    *-NonZero₁ m@{zero-int} {n} (inj-l pn)  = bot-elim (subst Pos (*-left-zeroᵉ n) pn)
    *-NonZero₁ m@{zero-int} {n} (inj-r nn)  = bot-elim (subst Neg (*-left-zeroᵉ n) nn)

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
