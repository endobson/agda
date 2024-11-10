{-# OPTIONS --cubical --safe --exact-split #-}

module finsubset.discrete.contains where

open import base
open import discrete
open import equality-path
open import equivalence
open import fin
open import finset
open import finset.instances
open import finset.search
open import finsubset
open import functions.embedding
open import hlevel
open import relation
open import set-quotient
open import truncation

module _ {ℓA : Level} {A : Type ℓA} {{discA : Discrete' A}} where
  opaque
    OrderedFinSubset-contains : (s : OrderedFinSubset A) -> (a : A) -> Dec (OrderedFinSubsetContains s a)
    OrderedFinSubset-contains (n , f , embed-f) a = handle search-result
      where
      search-result : ∥ (fiber f a) ∥ ⊎ (∀ i -> f i != a)
      search-result = finite-search-dec (Fin n , isFinSetⁱ) (\i -> decide-= (f i) a)

      handle : (∥ (fiber f a) ∥ ⊎ (∀ i -> f i != a)) -> Dec (fiber f a)
      handle (inj-l ∣fib∣) = yes (unsquash (eqFun isEmbedding-eq-hasPropFibers embed-f a) ∣fib∣)
      handle (inj-r ¬paths) = no (\ (i , path) -> ¬paths i path)

  FinSubset-contains : (s : FinSubset A) -> (a : A) -> Dec (FinSubsetContains s a)
  FinSubset-contains =
    SetQuotientElim.elimProp
      (\s -> isPropΠ (\a -> isPropDec (isProp-FinSubsetContains s a)))
      OrderedFinSubset-contains
