{-# OPTIONS --cubical --safe --exact-split #-}

module unordered-list where

open import base
open import equality

private
  variable
    ℓ : Level
    A B C : Type ℓ

data UnorderedList (A : Type ℓ) : Type ℓ
  where 
  [] : UnorderedList A
  _::_  : (a : A) -> UnorderedList A -> UnorderedList A
  swap : (a b : A) -> (l : UnorderedList A) -> (a :: (b :: l)) == (b :: (a :: l))

map : (A -> B) -> UnorderedList A -> UnorderedList B
map f [] = []
map f (e :: l) = f e :: (map f l)
map f (swap a b l i) = swap (f a) (f b) (map f l) i

