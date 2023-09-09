{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.constructions.lift
open import category.constructions.product
open import category.instances.terminal

module category.constructions.iterated-product where


module _ {ℓCo ℓCm : Level} (C : PreCategory ℓCo ℓCm) where
  open CategoryHelpers C

  IteratedProductC : (n : Nat) -> PreCategory ℓCo ℓCm
  IteratedProductC 0 = LiftC ℓCo ℓCm TermC
  IteratedProductC (suc n) = 
    ProductCat C (IteratedProductC n)
