{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.small where

open import finite-commutative-monoid
open import commutative-monoid
open import base
open import finset
open import finset.instances
open import finset.instances.base
open import isomorphism
open import equivalence
open import fin-algebra
open import fin
open import equality

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


  module _ {ℓA : Level} {A : Type ℓA} {{fsA : FinSetStr A}} where
    finiteMerge-0elem : (Iso A (Fin 0)) -> (f : A -> D) -> finiteMerge CM f == ε
    finiteMerge-0elem i f =
      finiteMerge-convert-iso CM (iso⁻¹ i) f >=>
      finiteMerge-Fin0 _

    finiteMerge-1elem : (i : Iso A (Fin 1)) -> (f : A -> D) ->
                        finiteMerge CM f == f (Iso.inv i zero-fin)
    finiteMerge-1elem i f =
      finiteMerge-convert-iso CM (iso⁻¹ i) f >=>
      finiteMerge-Fin1 _

    finiteMerge-2elem : (i : Iso A (Fin 2)) -> (f : A -> D) ->
                        finiteMerge CM f == f (Iso.inv i zero-fin) ∙ f (Iso.inv i (suc-fin zero-fin))
    finiteMerge-2elem i f =
      finiteMerge-convert-iso CM (iso⁻¹ i) f >=>
      finiteMerge-Fin2 _
