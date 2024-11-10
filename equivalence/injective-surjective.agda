{-# OPTIONS --cubical --safe --exact-split #-}

module equivalence.injective-surjective where

open import base
open import equality
open import equivalence
open import functions
open import functions.embedding
open import hlevel
open import sigma.base
open import truncation

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {f : A -> B} where
  opaque
    isEmbedding-isSurjective->isEquiv : isEmbedding f -> isSurjective f -> isEquiv f
    isEmbedding-isSurjective->isEquiv embed surj =
      record { equiv-proof = isContr-fib }
      where
      isProp-fib : ∀ b -> isProp (fiber f b)
      isProp-fib b = eqFun isEmbedding-eq-hasPropFibers embed b

      isContr-fib : ∀ b -> isContr (fiber f b)
      isContr-fib b = unsquash (isProp-fib b) (surj b) , (isProp-fib b) _

    isSet-isInjective->isEmbedding : isSet B -> isInjective f -> isEmbedding f
    isSet-isInjective->isEmbedding isSet-B inj-f =
      eqInv isEmbedding-eq-hasPropFibers isProp-fib
      where
      isProp-fib : ∀ b -> isProp (fiber f b)
      isProp-fib b (a1 , p1) (a2 , p2) = ΣProp-path (isSet-B _ _) (inj-f (p1 >=> sym p2))
