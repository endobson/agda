{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-semigroup.small where

open import base
open import semigroup
open import equivalence
open import equality
open import finset.inhabited
open import finset.instances.base
open import finite-commutative-semigroup
open import fin-algebra
open import type-algebra

module _ {ℓD : Level} {D : Type ℓD} (CS : CommutativeSemigroupStr D) where
  open CommutativeSemigroupStr CS

  private
    finite⁺Merge-Top : (f : Top -> D) -> finite⁺Merge CS f == f tt
    finite⁺Merge-Top f = finite⁺Merge-eval CS (equiv⁻¹ Fin-Top-eq) f

  module _ {ℓ : Level} {A : Type ℓ} {{FS-A : Fin⁺SetStr A}} where
    opaque
      finite⁺Merge-isContr : (isContr-A : isContr A) -> (f : A -> D) ->
                             finite⁺Merge CS f == f ⟨ isContr-A ⟩
      finite⁺Merge-isContr isContr-A f =
        finite⁺Merge-convert CS (equiv⁻¹ (Contr-Top-eq isContr-A)) f >=>
        finite⁺Merge-Top _ >=>
        cong f (snd isContr-A _)
