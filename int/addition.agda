{-# OPTIONS --cubical --safe --exact-split #-}

module int.addition where

open import base
open import equality-path
open import int.add1
open import int.base
open import int.elimination

open EqReasoning

_+ᵉ_ : Int -> Int -> Int
(nonneg m) +ᵉ n = (rec m)
  where rec : Nat -> Int
        rec zero = n
        rec (suc m) = add1 ((nonneg m) +ᵉ n)
(neg m) +ᵉ n = sub1 (rec m)
  where rec : Nat -> Int
        rec zero = n
        rec (suc m) = (neg m) +ᵉ n

opaque
  _ℤ+_ : Int -> Int -> Int
  _ℤ+_ = _+ᵉ_

opaque
  unfolding _ℤ+_

  ℤ+-eval : {m n : Int} -> m ℤ+ n == m +ᵉ n
  ℤ+-eval = refl

  add1-extract-left : {m n : Int} -> add1 m ℤ+ n == add1 (m ℤ+ n)
  sub1-extract-left : {m n : Int} -> sub1 m ℤ+ n == sub1 (m ℤ+ n)
  add1-extract-left {nonneg m'} = refl
  add1-extract-left {neg zero} {n} = (sym (add1-sub1-id {n}))
  add1-extract-left {neg (suc m')} {n} =
    begin
      add1 (neg (suc m')) ℤ+ n
    ==<>
      neg m' ℤ+ n
    ==< sym (add1-sub1-id {neg m' ℤ+ n}) >
      add1 (sub1 (neg m' ℤ+ n))
    ==< cong add1 (sym (sub1-extract-left {neg m'})) >
      add1 (sub1 (neg m') ℤ+ n)
    ==<>
      add1 ((neg (suc m')) ℤ+ n)
    end

  sub1-extract-left {zero-int} = refl
  sub1-extract-left {neg m'} = refl
  sub1-extract-left {nonneg (suc m')} {n} =
    begin
     sub1 (nonneg (suc m')) ℤ+ n
    ==<>
     nonneg m' ℤ+ n
    ==< sym (sub1-add1-id {nonneg m' ℤ+ n}) >
     sub1 (add1 (nonneg m' ℤ+ n))
    ==< cong sub1 (sym (add1-extract-left {nonneg m'})) >
     sub1 (add1 (nonneg m') ℤ+ n)
    ==<>
     sub1 ((nonneg (suc m')) ℤ+ n)
    end

  ℤ+-right : {m n p : Int} -> (n == p) -> m ℤ+ n == m ℤ+ p
  ℤ+-right {m} id = cong (\x -> m ℤ+ x) id

  ℤ+-left : {m n p : Int} -> (n == p) -> n ℤ+ m == p ℤ+ m
  ℤ+-left {m} id = cong (\x -> x ℤ+ m) id

  ℤ+-left-zero : (m : Int) -> (zero-int ℤ+ m) == m
  ℤ+-left-zero _ = refl

  ℤ+-right-zero : (m : Int) -> (m ℤ+ zero-int) == m
  ℤ+-right-zero =
    IntElim-add1sub1-elim refl
      (\m p -> add1-extract-left {m} {zero-int} >=> cong add1 p)
      (\m p -> sub1-extract-left {m} {zero-int} >=> cong sub1 p)

opaque
  add1-extract-right : {m n : Int} -> m ℤ+ add1 n == add1 (m ℤ+ n)
  add1-extract-right {m} {n} =
    IntElim-add1sub1-elim {P = \m -> (m ℤ+ add1 n) == add1 (m ℤ+ n)}
      (ℤ+-left-zero _ >=> cong add1 (sym (ℤ+-left-zero _)))
      (\m p -> add1-extract-left >=> cong add1 p >=>
               cong add1 (sym add1-extract-left))
      (\m p -> sub1-extract-left >=> cong sub1 p >=>
               sub1-add1-id >=> sym add1-sub1-id >=>
               cong add1 (sym sub1-extract-left))
      m

  sub1-extract-right : {m n : Int} -> m ℤ+ sub1 n == sub1 (m ℤ+ n)
  sub1-extract-right {m} {n} =
    IntElim-add1sub1-elim {P = \m -> (m ℤ+ sub1 n) == sub1 (m ℤ+ n)}
      (ℤ+-left-zero _ >=> cong sub1 (sym (ℤ+-left-zero _)))
      (\m p -> add1-extract-left >=> cong add1 p >=>
               add1-sub1-id >=> sym sub1-add1-id >=>
               cong sub1 (sym add1-extract-left))
      (\m p -> sub1-extract-left >=> cong sub1 p >=>
               cong sub1 (sym sub1-extract-left))
      m
