{-# OPTIONS --cubical --safe --exact-split #-}

module unordered-list.base where

open import base
open import cubical
open import equality
open import hlevel

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _::_
data UList (A : Type ℓ) : Type ℓ
  where
  [] : UList A
  _::_  : (a : A) -> UList A -> UList A
  swap : (a b : A) -> (l : UList A) -> (a :: (b :: l)) == (b :: (a :: l))
  trunc : isSet (UList A)

-- Elimination functions

module UListElim where

  module _ {ℓ} {B : UList A -> Type ℓ}
    (trunc* : {as : UList A} -> isSet (B as))
    ([]* : B [])
    (_::*_ : (a : A) -> {as : UList A} -> B as -> B (a :: as))
    (swap* : (a1 a2 : A) -> {as : UList A} -> (bs : B as)
             -> PathP (\ i -> B (swap a1 a2 as i)) (a1 ::* (a2 ::* bs)) (a2 ::* (a1 ::* bs)))
    where

    full : (as : UList A) -> (B as)
    full [] = []*
    full (a :: as) = a ::* (full as)
    full (swap a1 a2 as i) = (swap* a1 a2 (full as) i)
    full (trunc as1 as2 p q i j) =
      isOfHLevel->isOfHLevelDep 2 (\_ -> trunc*) (full as1) (full as2) (cong full p) (cong full q)
                                (trunc as1 as2 p q) i j

  module _ {ℓ} {B : UList A -> Type ℓ}
    (BProp : {as : UList A} -> isProp (B as))
    ([]* : B [])
    (_::*_ : (a : A) -> {as : UList A} -> B as -> B (a :: as))
    where
    private
      swap* : (a1 a2 : A) -> {as : UList A} -> (bs : B as)
              -> PathP (\ i -> B (swap a1 a2 as i)) (a1 ::* (a2 ::* bs)) (a2 ::* (a1 ::* bs))
      swap* a1 a2 {as} bs =
        toPathP (BProp
                  (transp (\ i -> B (swap a1 a2 as i)) i0 (a1 ::* (a2 ::* bs)))
                  (a2 ::* (a1 ::* bs)))
      trunc* : {as : UList A} -> isSet (B as)
      trunc* = isProp->isSet BProp

    prop : (as : UList A) -> (B as)
    prop = full {B = B} trunc* []* _::*_ swap*

  module _ {ℓ} {B : Type ℓ}
    (BSet* : isSet B)
    ([]* : B)
    (_::*_ : A -> B -> B)
    (swap* : (a0 a1 : A) (b : B) -> (a0 ::* (a1 ::* b)) == (a1 ::* (a0 ::* b)))
    where

    rec : (as : UList A) -> B
    rec [] = []*
    rec (a :: as) = a ::* (rec as)
    rec (swap a1 a2 as i) = (swap* a1 a2 (rec as) i)
    rec (trunc as1 as2 p q i j) = (BSet* (rec as1) (rec as2) (cong rec p) (cong rec q) i j)
