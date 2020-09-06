{-# OPTIONS --cubical --safe --exact-split #-}

module list.permutation where

open import base
open import equality
open import list.base

private
  variable
    ℓ : Level
    A : Type ℓ

data Permutation (A : Type ℓ) : (List A) -> (List A) -> Type ℓ where
  permutation-empty : Permutation A [] []
  permutation-cons : (a : A) -> {as1 as2 : List A} -> Permutation A as1 as2
                     -> Permutation A (a :: as1) (a :: as2)
  permutation-swap : (a1 a2 : A) -> (as : List A)
                     -> Permutation A (a1 :: a2 :: as) (a2 :: a1 :: as)
  permutation-compose : {as1 as2 as3 : List A}
                        -> Permutation A as1 as2 -> Permutation A as2 as3
                        -> Permutation A as1 as3

permutation-same : (as : List A) -> Permutation A as as
permutation-same []        = permutation-empty
permutation-same (a :: as) = permutation-cons a (permutation-same as)

permutation-== : {as bs : List A} -> as == bs -> Permutation A as bs
permutation-== {A = A} {as = as} p = transport (\i -> Permutation A as (p i)) (permutation-same as)

insert : (A -> A -> Boolean) -> A -> List A -> List A
insert _ a [] = a :: []
insert _<_ a (a2 :: as) with a < a2
... | true = a :: (a2 :: as)
... | false = a2 :: (insert _<_ a as)


Permutation-insert : (_<_ : A -> A -> Boolean) -> (a : A) -> (as : (List A))
                      -> Permutation A (a :: as) (insert _<_ a as)
Permutation-insert _t a [] = permutation-same [ a ]
Permutation-insert _<_ a (a2 :: as) with a < a2
... | true = permutation-same (a :: a2 :: as)
... | false =
  permutation-compose
    (permutation-swap a a2 _)
    (permutation-cons a2 (Permutation-insert _<_ a as))

insertion-sort : (A -> A -> Boolean) -> List A -> List A
insertion-sort _<_ [] = []
insertion-sort _<_ (a :: as) = (insert _<_ a (insertion-sort _<_ as))

Permutation-insertion-sort : (_<_ : A -> A -> Boolean) -> (as : List A)
                             -> Permutation A as (insertion-sort _<_ as)
Permutation-insertion-sort _<_ [] = permutation-empty
Permutation-insertion-sort _<_ (a :: as) =
  (permutation-compose
    (permutation-cons a (Permutation-insertion-sort _<_ as))
    (Permutation-insert _<_ a _))

permutation-flip : {as bs : List A} -> Permutation A as bs -> Permutation A bs as
permutation-flip permutation-empty = permutation-empty
permutation-flip (permutation-cons a p) =
  permutation-cons a (permutation-flip p)
permutation-flip (permutation-swap a b p) = permutation-swap b a p
permutation-flip (permutation-compose p1 p2) =
  permutation-compose (permutation-flip p2) (permutation-flip p1)

permutation-length== : {as bs : List A} -> Permutation A as bs -> length as == length bs
permutation-length== (permutation-empty) = refl
permutation-length== (permutation-cons _ p) = cong suc (permutation-length== p)
permutation-length== (permutation-swap a b l) = refl
permutation-length== (permutation-compose p1 p2) = permutation-length== p1 >=> permutation-length== p2

permutation-snoc : (a : A) (bs : List A) -> Permutation A ([ a ] ++ bs) (bs ++ [ a ])
permutation-snoc a []        = permutation-same [ a ]
permutation-snoc a (b :: bs) =
  permutation-compose (permutation-swap a b bs) (permutation-cons b (permutation-snoc a bs))

permutation-++-left : {as bs : List A} -> Permutation A as bs -> (cs : List A)
                      -> Permutation A (as ++ cs) (bs ++ cs)
permutation-++-left permutation-empty cs = permutation-same cs
permutation-++-left (permutation-cons a p) cs =
  permutation-cons a (permutation-++-left p cs)
permutation-++-left (permutation-swap a b l) cs =
  permutation-swap a b (l ++ cs)
permutation-++-left (permutation-compose p1 p2) cs =
  permutation-compose
    (permutation-++-left p1 cs)
    (permutation-++-left p2 cs)

permutation-++-swap :
  (a : A) (as bs : List A) -> Permutation A ((a :: as) ++ bs) (as ++ (a :: bs))
permutation-++-swap {A = A} a [] bs         = permutation-same (a :: bs)
permutation-++-swap {A = A} a (a2 :: as) bs =
  permutation-compose
    (permutation-swap a a2 (as ++ bs))
    (permutation-cons a2 (permutation-++-swap a as bs))
