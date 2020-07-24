{-# OPTIONS --cubical --safe --exact-split #-}

module list.unordered where

open import base
open import equality
open import relation
open import list
open import list.discrete
open import nat

import unordered-list as ul
import unordered-list.discrete as ul

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

unorder-contains : {a : A} {l : List A} -> contains a l -> ul.contains a (unorder l)
unorder-contains {a = a} {[]} c = bot-elim ([]-¬contains c)
unorder-contains {a = a} {a2 :: as} ([] , r , p) = (unorder r , cong unorder p)
unorder-contains {a = a} {a2 :: as} (_ :: l , r , p) =
  handle (unorder-contains (l , r , ::-injective p))
  where
  handle : (ul.contains a (unorder as)) -> (ul.contains a (unorder (a2 :: as)))
  handle (bs , p) = (a2 ul.:: bs , (ul.swap a a2 bs) >=> (cong (a2 ul.::_) p))

module _ {ℓA : Level} {A : Type ℓA} {{disc'A : Discrete' A}} where

  private
    discA = Discrete'.f disc'A

  unorder-count : (a : A) (l : List A) -> count a l == ul.count a (unorder l)
  unorder-count a [] = refl
  unorder-count a (a2 :: as) = handle (discA a a2)
    where
    handle : (Dec (a == a2)) -> count a (a2 :: as) == ul.count a (unorder (a2 :: as))
    handle (yes p) =
      count-== as p
      >=> cong suc (unorder-count a as)
      >=> (sym (ul.count-== (unorder as) p))
    handle (no p) =
      count-!= as p
      >=> (unorder-count a as)
      >=> (sym (ul.count-!= (unorder as) p))

  unorder-contains' : {a : A} {l : List A} -> ul.contains a (unorder l) -> contains a l
  unorder-contains' {a} {l} c = count-suc->contains (sym (snd pos-count) >=> +'-right-suc)
    where
    pos-count : (count a l) > 0
    pos-count = transport (\i -> unorder-count a l (~ i) > 0) (ul.contains->count>0 c)
