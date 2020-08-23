{-# OPTIONS --cubical --safe --exact-split #-}

module list.base where

open import base

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _::_
data List (A : Type ℓ) : Type ℓ where
  [] : List A
  _::_  : (a : A) -> List A -> List A

[_] : A -> List A
[ a ] = a :: []
