{-# OPTIONS --cubical --safe --exact-split #-}

module finsubset where

open import base
open import equivalence
open import fin
open import functions
open import functions.embedding
open import hlevel
open import nat
open import relation
open import set-quotient

OrderedFinSubset : {ℓ : Level} -> Type ℓ -> Type ℓ
OrderedFinSubset A = Σ[ n ∈ ℕ ] (Fin n ↪ A)

module _ {ℓA : Level} {A : Type ℓA} where
  OrderedFinSubsetContains : OrderedFinSubset A -> A -> Type ℓA
  OrderedFinSubsetContains (_ , f , _) a = fiber f a

  OrderedFinSubset~ : Rel (OrderedFinSubset A) ℓA
  OrderedFinSubset~ s1 s2 = ∀ a -> OrderedFinSubsetContains s1 a ≃ OrderedFinSubsetContains s2 a

  opaque
    isEquivRel-OrderedFinSubset~ : isEquivRel OrderedFinSubset~
    isEquivRel-OrderedFinSubset~ .isEquivRel.reflexive a = idEquiv _
    isEquivRel-OrderedFinSubset~ .isEquivRel.symmetric ~ a = equiv⁻¹ (~ a)
    isEquivRel-OrderedFinSubset~ .isEquivRel.transitive ~₁ ~₂ a = ~₁ a >eq> ~₂ a

    isProp-OrderedFinSubset~ : ∀ x y -> isProp (OrderedFinSubset~ x y)
    isProp-OrderedFinSubset~ (_ , _ , e1) (_ , _ , e2) =
      isPropΠ (\a -> isProp-≃ (eqFun isEmbedding-eq-hasPropFibers e1 a)
                            (eqFun isEmbedding-eq-hasPropFibers e2 a))

module _ {ℓ : Level} (A : Type ℓ) where
  FinSubset : Type ℓ
  FinSubset = OrderedFinSubset A / OrderedFinSubset~
