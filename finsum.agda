{-# OPTIONS --cubical --safe --exact-split #-}

module finsum where

open import additive-group
open import base
open import equivalence
open import fin
open import finite-commutative-monoid
open import finset
open import functions
open import isomorphism

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM

  finSumDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finSumDep = finMergeDep CM

  enumerationSum : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationSum = enumerationMerge CM

  equivSum : {n : Nat} -> (A ≃ Fin n) -> (A -> D) -> D
  equivSum = equivMerge CM

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    finiteSum : (I -> D) -> D
    finiteSum = finiteMerge CM

  finiteSumᵉ : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
  finiteSumᵉ (_ , f) = finiteMerge CM {{FI = record {isFin = f} }}

  abstract
    finiteSumᵉ-eval : {ℓ : Level} (A : FinSet ℓ) {n : Nat}
                      -> (eq : (⟨ A ⟩ ≃ Fin n)) -> (f : ⟨ A ⟩ -> D)
                      -> finiteSumᵉ A f == equivSum eq f
    finiteSumᵉ-eval = finiteMergeᵉ-eval CM

    finiteSumᵉ-convert : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                         (eq : (⟨ B ⟩ ≃ ⟨ A ⟩) ) (f : ⟨ A ⟩ -> D)
                         -> finiteSumᵉ A f == finiteSumᵉ B (f ∘ (eqFun eq))
    finiteSumᵉ-convert = finiteMergeᵉ-convert CM

    finiteSumᵉ-convert-iso : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                             (i : Iso ⟨ B ⟩ ⟨ A ⟩) (f : ⟨ A ⟩ -> D)
                             -> finiteSumᵉ A f == finiteSumᵉ B (f ∘ (Iso.fun i))
    finiteSumᵉ-convert-iso = finiteMergeᵉ-convert-iso CM
