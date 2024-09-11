{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.sum-pair where

open import base
open import commutative-monoid
open import equality
open import fin.sum-pair
open import fin.sum-pair.without-zero
open import finite-commutative-monoid
open import finite-commutative-monoid.without-point
open import finset.instances.sum-pair
open import finset.without-point
open import functions

module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  opaque
    finiteMerge-FinPair+-split₁ :
      {n : Nat} (f : FinPair+ (suc n) -> D) ->
      finiteMerge CM f == f fin-pair+-zero₁ ∙ finiteMerge CM (f ∘ fin-pair+-suc₁)
    finiteMerge-FinPair+-split₁ f =
      finiteMerge-WithoutPoint CM fin-pair+-zero₁ f >=>
      ∙-right (finiteMerge-convert-iso CM fin-pair+-suc₁-Iso _)

    finiteMerge-FinPair+-split₂ :
      {n : Nat} (f : FinPair+ (suc n) -> D) ->
      finiteMerge CM f == f fin-pair+-zero₂ ∙ finiteMerge CM (f ∘ fin-pair+-suc₂)
    finiteMerge-FinPair+-split₂ f =
      finiteMerge-WithoutPoint CM fin-pair+-zero₂ f >=>
      ∙-right (finiteMerge-convert-iso CM fin-pair+-suc₂-Iso _)
