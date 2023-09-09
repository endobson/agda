{-# OPTIONS --cubical --safe --exact-split #-}

module category.example where

open import base
open import nat
open import category.base
open import category.displayed
open import category.monoidal.base
open import category.constructions.iterated-product
open import category.instances.discrete
open import category.instances.finset
open import category.instances.set


ℕC : PreCategory ℓ-zero ℓ-zero
ℕC = DiscreteC isSetNat

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) (M : MonoidalStr C) where
  open CategoryHelpers C
  open MonoidalStrHelpers M

  PC : (n : Nat) -> PreCategory ℓO ℓM
  PC n = IteratedProductC C n

  C2 : PreCategoryᴰ (FinSetC ℓ-zero) ℓO ℓM
  C2 .PreCategoryᴰ.Objᴰ ((S , _) , _) = S -> Obj C
  C2 .PreCategoryᴰ.Morᴰ (set-function f , tt) cs1 cs2 =
    ∀ s -> C [ cs1 s , cs2 (f s) ]

  C3 : PreCategoryᴰ (TotalC C2) _ _
  C3 .PreCategoryᴰ.Objᴰ (((S , _) , _) , cs) = 
    Σ[ o ∈ Obj C ] (∀ s -> C [ cs s , o ]) 
  C3 .PreCategoryᴰ.Morᴰ ((set-function f , tt) , ms) o1 o2 = ?
    
