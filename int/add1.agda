{-# OPTIONS --cubical --safe --exact-split #-}

module int.add1 where

open import int.base
open import base

add1 : Int -> Int
add1 (nonneg x) = (nonneg (suc x))
add1 (neg zero) = (nonneg zero)
add1 (neg (suc x)) = (neg x)

sub1 : Int -> Int
sub1 (nonneg zero) = neg zero
sub1 (nonneg (suc n)) = nonneg n
sub1 (neg n) = (neg (suc n))

abstract
  add1-sub1-id : {n : Int} -> add1 (sub1 n) == n
  add1-sub1-id {zero-int} = refl
  add1-sub1-id {pos n'} = refl
  add1-sub1-id {neg zero} = refl
  add1-sub1-id {neg (suc x)} = refl

  sub1-add1-id : {n : Int} -> sub1 (add1 n) == n
  sub1-add1-id {nonneg n} = refl
  sub1-add1-id {neg zero} = refl
  sub1-add1-id {neg (suc n')} = refl

add1-minus->minus-sub1 : {n : Int} -> add1 (ℤ- n) == ℤ- (sub1 n)
add1-minus->minus-sub1 {neg zero} = refl
add1-minus->minus-sub1 {neg (suc n)} = refl
add1-minus->minus-sub1 {nonneg zero} = refl
add1-minus->minus-sub1 {nonneg (suc zero)} = refl
add1-minus->minus-sub1 {nonneg (suc (suc _))} = refl

sub1-minus->minus-add1 : {n : Int} -> sub1 (ℤ- n) == ℤ- (add1 n)
sub1-minus->minus-add1 {nonneg zero} = refl
sub1-minus->minus-add1 {nonneg (suc n')} = refl
sub1-minus->minus-add1 {neg zero} = refl
sub1-minus->minus-add1 {neg (suc n')} = refl
