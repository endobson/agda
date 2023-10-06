{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.constructions.opposite
open import category.constructions.product
open import category.functor
open import category.hom-functor
open import category.instances.set
open import category.natural-transformation

module category.adjoint where

module _ {ℓ : Level} {C : PreCategory ℓ ℓ} {D : PreCategory ℓ ℓ}
         (L : Functor C D) (R : Functor D C) where
  private
    H1 : Functor (ProductCat (OpCat C) D) (SetC ℓ)
    H1 = (product-functor (op-functor L) (idF D)) ⋆F (hom-functor D)

    H2 : Functor (ProductCat (OpCat C) D) (SetC ℓ)
    H2 = (product-functor (idF (OpCat C)) R) ⋆F (hom-functor C)

  record isAdjointPair : Type (ℓ-suc ℓ) where
    field
      adj-natural : NaturalTransformation H1 H2
