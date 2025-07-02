{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.hedberg where

open import base
open import cubical
open import equality-path
open import hlevel.base
open import relation

private
  variable
    ℓ : Level
    A : Type ℓ

opaque
  -- Hedberg's Theorem
  Stable==->isSet : ((x y : A) -> Stable (x == y)) -> isSet A
  Stable==->isSet {A = A} st a0 a1 p1 p2 j i =
    let
     -- Push through the stabilizer
     f : (x : A) -> a0 == x -> a0 == x
     f x p = st a0 x (\h -> h p)
     -- Pushing through the stabilizer is a constant function
     fIsConst : (x : A) -> (p q : a0 == x) -> f x p == f x q
     fIsConst x p q i = st a0 x (isProp¬ (\h -> h p) (\h -> h q) i)
     -- Shows that we can extend to any path starting from refl
     rem : (p : a0 == a1) -> PathP (\i -> a0 == p i) (f a0 refl) (f a1 p)
     rem p j = f (p j) (\ i -> p (i ∧ j))

    in hcomp (\ k -> (\ { (i = i0) -> f a0 refl k
                        ; (i = i1) -> fIsConst a1 p1 p2 j k
                        ; (j = i0) -> rem p1 i k
                        ; (j = i1) -> rem p2 i k})) a0
