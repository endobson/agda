{-# OPTIONS --cubical --safe --exact-split #-}

module category.natural-isomorphism where

open import base
open import category.base
open import category.isomorphism
open import hlevel.base

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
  (F G : Functor C D) where

  isNaturalIso : NaturalTransformation F G -> Type _
  isNaturalIso nt = ∀ c -> isIso D (NT-obj nt c)

  isProp-isNaturalIso : {nt : NaturalTransformation F G} -> isProp (isNaturalIso nt)
  isProp-isNaturalIso = isPropΠ (\_ -> isProp-isIso)

  NaturalIsomorphism : Type _
  NaturalIsomorphism = Σ (NaturalTransformation F G) isNaturalIso
