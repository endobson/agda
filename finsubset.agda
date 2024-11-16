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
open import sigma.base
open import univalence

OrderedFinSubset : {ℓ : Level} -> Type ℓ -> Type ℓ
OrderedFinSubset A = Σ[ n ∈ ℕ ] (Fin n ↪ A)

module _ {ℓA : Level} {A : Type ℓA} where
  OrderedFinSubsetContains : OrderedFinSubset A -> A -> Type ℓA
  OrderedFinSubsetContains (_ , f , _) a = fiber f a

  opaque
    isProp-OrderedFinSubsetContains :
      (s : OrderedFinSubset A) (a : A) -> isProp (OrderedFinSubsetContains s a)
    isProp-OrderedFinSubsetContains (_ , _ , e) a =
      eqFun isEmbedding-eq-hasPropFibers e a

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

module _ {ℓA : Level} {A : Type ℓA} where
  private
    FinSubsetContainsΣ : A -> FinSubset A -> hProp ℓA
    FinSubsetContainsΣ a =
      SetQuotientElim.rec isSet-hProp
        (\as -> OrderedFinSubsetContains as a , isProp-OrderedFinSubsetContains as a)
        (\as1 as2 as~ -> ΣProp-path isProp-isProp (ua (as~ a)))


  FinSubsetContains : FinSubset A -> A -> Type ℓA
  FinSubsetContains as a = fst (FinSubsetContainsΣ a as)
  isProp-FinSubsetContains : (as : FinSubset A) -> (a : A) -> isProp (FinSubsetContains as a)
  isProp-FinSubsetContains as a = snd (FinSubsetContainsΣ a as)

  opaque
    FinSubsetContains-path : (as1 as2 : FinSubset A) ->
      (∀ a -> FinSubsetContains as1 a ≃ FinSubsetContains as2 a) ->
      as1 == as2
    FinSubsetContains-path =
      SetQuotientElim.elimProp2
        (\as1 as2 -> isPropΠ (\_ -> squash/ as1 as2))
        (\as1 as2 -> eq/ as1 as2)
