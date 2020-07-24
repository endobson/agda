{-# OPTIONS --cubical --safe --exact-split #-}

module list.unordered where

open import base
open import equality
open import list
import unordered-list as ul

private
  variable
    ℓ : Level
    A : Type ℓ


-- Conversion to unorderd lists
unorder : List A -> ul.UList A
unorder []        = ul.[]
unorder (a :: as) = a ul.:: (unorder as)

unorder-permutation : {as bs : List A} -> Permutation A as bs -> (unorder as) == (unorder bs)
unorder-permutation permutation-empty         = refl
unorder-permutation (permutation-cons a p)    = cong (a ul.::_) (unorder-permutation p)
unorder-permutation (permutation-swap a b as) = ul.swap a b (unorder as)
unorder-permutation (permutation-compose p q) = unorder-permutation p >=> unorder-permutation q
