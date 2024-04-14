{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.small where

open import base
open import commutative-monoid
open import equality
open import equivalence
open import fin
open import fin-algebra
open import fin-algebra
open import finite-commutative-monoid
open import finset
open import finset.instances
open import type-algebra
open import type-algebra.boolean
open import finset.instances.boolean
open import finset.instances.base
open import isomorphism

module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  private
    finiteMerge' = finiteMerge CM
    equivMerge' = equivMerge CM
    finiteMerge-convert' = finiteMerge-convert CM
    enumerationMerge' = enumerationMerge CM
    eval = finiteMerge-eval CM

  opaque
    finiteMerge-Bot : (f : Bot -> D) -> finiteMerge' f == ε
    finiteMerge-Bot = eval (equiv⁻¹ Fin-Bot-eq)

    finiteMerge-Top : (f : Top -> D) -> finiteMerge' f == f tt
    finiteMerge-Top f = eval (equiv⁻¹ Fin-Top-eq) f >=> ∙-right-ε

    finiteMerge-Fin0 : (f : (Fin 0) -> D) -> finiteMerge' f == ε
    finiteMerge-Fin0 = eval (idEquiv _)

    finiteMerge-Fin1 : (f : (Fin 1) -> D) -> finiteMerge' f == f zero-fin
    finiteMerge-Fin1 f = eval (idEquiv _) f >=> ∙-right-ε

    private
      finiteMerge-Fin2 : (f : (Fin 2) -> D) -> finiteMerge' f ==
                                               (f zero-fin) ∙ (f (suc-fin zero-fin))
      finiteMerge-Fin2 f = eval (idEquiv _) f >=> sym ∙-assoc >=> ∙-right-ε

      finiteMerge-Boolean : (f : Boolean -> D) -> finiteMerge' f == (f true) ∙ (f false)
      finiteMerge-Boolean f = eval (equiv⁻¹ Fin2≃Boolean) f >=> sym ∙-assoc >=> ∙-right-ε

  module _ {ℓA : Level} {A : Type ℓA} {{fsA : FinSetStr A}} where
    -- Zero elements
    finiteMerge-Uninhabited : (¬ A) -> (f : A -> D) -> finiteMerge' f == ε
    finiteMerge-Uninhabited ¬a f =
      finiteMerge-convert' (equiv⁻¹ (¬-Bot-eq ¬a)) f >=>
      finiteMerge-Bot _

    -- One element
    finiteMerge-isContr :
      (isContr-A : isContr A) -> (f : A -> D) -> finiteMerge' f == f ⟨ isContr-A ⟩
    finiteMerge-isContr isContr-A f = path
      where
      a : A
      a = fst (isContr-A)

      A≃Top : A ≃ Top
      A≃Top = Contr-Top-eq isContr-A

      path : finiteMerge' f == f a
      path =
        finiteMerge-convert' (equiv⁻¹ A≃Top) f >=>
        finiteMerge-Top (\_ -> f a)

    -- Two elements
    finiteMerge-2elem : (i : Iso A Boolean) -> (f : A -> D) ->
                        finiteMerge CM f == f (Iso.inv i true) ∙ f (Iso.inv i false)
    finiteMerge-2elem i f =
      finiteMerge-convert-iso CM (iso⁻¹ i) f >=>
      finiteMerge-Boolean _
