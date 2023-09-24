{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.constructions.opposite
open import category.constructions.product
open import category.hom-functor
open import category.instances.set
open import category.instances.small

module category.adjoint where

module _ {ℓ : Level} {C : PreCategory ℓ ℓ} {D : PreCategory ℓ ℓ}
         (L : Functor C D) (R : Functor D C) where
  private
    H1 : Functor (ProductCat (OpCat C) D) (SetC ℓ)
    H1 = functor-compose (product-functor (op-functor L) (id-functor D)) (hom-functor D)

    H2 : Functor (ProductCat (OpCat C) D) (SetC ℓ)
    H2 = functor-compose (product-functor (id-functor (OpCat C)) R) (hom-functor C)

  record isAdjointPair : Type (ℓ-suc ℓ) where
    field
      adj-natural : NaturalTransformation H1 H2
