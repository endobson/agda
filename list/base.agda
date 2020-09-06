{-# OPTIONS --cubical --safe --exact-split #-}

module list.base where

open import base

private
  variable
    ℓ : Level
    A B : Type ℓ

infixr 5 _::_
data List (A : Type ℓ) : Type ℓ where
  [] : List A
  _::_  : (a : A) -> List A -> List A

[_] : A -> List A
[ a ] = a :: []

infixr 5 _++_
_++_ : List A -> List A -> List A
[] ++ l2 = l2
(a :: l1) ++ l2 = a :: (l1 ++ l2)

map : (A -> B) -> List A -> List B
map f [] = []
map f (e :: l) = f e :: (map f l)

length : (l : List A) -> Nat
length []        = 0
length (_ :: as) = suc (length as)
