{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.small where

open import base
open import commutative-monoid
open import equality-path
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid
open import finset
open import finset.instances
open import finset.instances.base
open import finset.instances.boolean
open import isomorphism
open import type-algebra
open import type-algebra.boolean

module _ {ℓD : Level} {D : Type ℓD} {CM : CommMonoid D} where
  open CommMonoid CM

  opaque
    finiteMerge-Bot : {f : Bot -> D} -> finiteMerge CM f == ε
    finiteMerge-Bot = finiteMerge-eval (equiv⁻¹ Fin-Bot-eq)

    finiteMerge-Top : {f : Top -> D} -> finiteMerge CM f == f tt
    finiteMerge-Top = finiteMerge-eval (equiv⁻¹ Fin-Top-eq) >=> ∙-right-ε

    finiteMerge-Fin0 : {f : (Fin 0) -> D} -> finiteMerge CM f == ε
    finiteMerge-Fin0 = finiteMerge-eval (idEquiv _)

    finiteMerge-Fin1 : {f : (Fin 1) -> D} -> finiteMerge CM f == f zero-fin
    finiteMerge-Fin1 = finiteMerge-eval (idEquiv _) >=> ∙-right-ε

    private
      finiteMerge-Fin2 : {f : (Fin 2) -> D} -> finiteMerge CM f ==
                                               (f zero-fin) ∙ (f (suc-fin zero-fin))
      finiteMerge-Fin2 = finiteMerge-eval (idEquiv _) >=> sym ∙-assoc >=> ∙-right-ε

      finiteMerge-Boolean : {f : Boolean -> D} -> finiteMerge CM f == (f true) ∙ (f false)
      finiteMerge-Boolean = finiteMerge-eval (equiv⁻¹ Fin2≃Boolean) >=> sym ∙-assoc >=> ∙-right-ε

  module _ {ℓA : Level} {FA : FinSet ℓA} where
    private
      A : Type ℓA
      A = ⟨ FA ⟩

    -- Zero elements
    finiteMerge-Uninhabited : (¬ A) -> {f : A -> D} -> finiteMergeᵉ CM FA f == ε
    finiteMerge-Uninhabited ¬a =
      finiteMerge-convert (equiv⁻¹ (¬-Bot-eq ¬a)) >=>
      finiteMerge-Bot

    -- One element
    finiteMerge-isContr :
      (isContr-A : isContr A) -> {f : A -> D} -> finiteMergeᵉ CM FA f == f ⟨ isContr-A ⟩
    finiteMerge-isContr isContr-A {f} =
      finiteMerge-convert (equiv⁻¹ (Contr-Top-eq isContr-A)) >=>
      finiteMerge-Top

    -- Two elements
    finiteMerge-2elem : (i : Iso A Boolean) -> {f : A -> D} ->
                        finiteMergeᵉ CM FA f == f (Iso.inv i true) ∙ f (Iso.inv i false)
    finiteMerge-2elem i = finiteMerge-convert-iso (iso⁻¹ i) >=> finiteMerge-Boolean
