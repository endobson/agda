{-# OPTIONS --cubical --safe --exact-split #-}

module vec where

open import base

private
  variable
    ℓ : Level
    A B C : Type ℓ

infixr 5 _::_
data Vec (A : Type ℓ) : Nat -> Type ℓ where
  [] : Vec A 0
  _::_  : {n : Nat} (a : A) -> Vec A n -> Vec A (suc n)
