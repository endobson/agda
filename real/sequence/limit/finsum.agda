{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.finsum where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import finset
open import finset.instances
open import finsum
open import functions
open import funext
open import nat
open import real
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import truncation

private
  module _ {s : Fin 0 -> ℕ -> ℝ} {l : Fin 0 -> ℝ} where
    finiteSum-zero-preserves-limit :
      isLimit (\j -> finiteSum (\i -> s i j)) (finiteSum l)
    finiteSum-zero-preserves-limit =
      subst2 isLimit (funExt (\_ -> (sym (finiteMerge-Fin0 _ _)))) (sym (finiteMerge-Fin0 _ _))
        (isLimit-constant-seq 0#)

  module _ {n : Nat} {s : Fin (suc n) -> ℕ -> ℝ} {l : Fin (suc n) -> ℝ} where
    finiteSum-suc-preserves-limit :
      isLimit (s zero-fin) (l zero-fin) ->
      isLimit (\j -> finiteSum (\i -> s (suc-fin i) j)) (finiteSum (l ∘ suc-fin)) ->
      isLimit (\j -> finiteSum (\i -> s i j)) (finiteSum l)
    finiteSum-suc-preserves-limit lim-zero rec =
      subst2 isLimit (funExt (\j -> (sym (finiteMerge-FinSuc _ _)))) (sym (finiteMerge-FinSuc _ _))
        (+-preserves-limit lim-zero rec)

  finiteSum-Fin-preserves-limit : (n : Nat) {s : Fin n -> ℕ -> ℝ} {l : Fin n -> ℝ} ->
      (∀ i -> isLimit (s i) (l i)) ->
      isLimit (\j -> finiteSum (\i -> s i j)) (finiteSum l)
  finiteSum-Fin-preserves-limit zero _ =
    finiteSum-zero-preserves-limit
  finiteSum-Fin-preserves-limit (suc i) lims =
    finiteSum-suc-preserves-limit (lims zero-fin)
      (finiteSum-Fin-preserves-limit i (lims ∘ suc-fin))

module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}}
         {s : I -> ℕ -> ℝ} {l : I -> ℝ} where
  opaque
    finiteSum-preserves-limit :
      (∀ i -> isLimit (s i) (l i)) ->
      isLimit (\j -> finiteSum (\i -> s i j)) (finiteSum l)
    finiteSum-preserves-limit lims =
      unsquash isProp-isLimit (∥-map handle isFinSetⁱ)
      where
      handle : Σ[ n ∈ Nat ] (I ≃ Fin n) ->
                isLimit (\j -> finiteSum (\i -> s i j)) (finiteSum l)
      handle (n , eq) =
        subst2 isLimit (funExt (\j -> (sym (finiteMerge-convert _ (equiv⁻¹ eq) _))))
                       (sym (finiteMerge-convert _ (equiv⁻¹ eq) _))
          (finiteSum-Fin-preserves-limit n lims')
        where
        lims' : ∀ i -> isLimit (s (eqInv eq i)) (l (eqInv eq i))
        lims' = lims ∘ (eqInv eq)
