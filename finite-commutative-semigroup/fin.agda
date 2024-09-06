{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-semigroup.fin where

open import base
open import equality
open import equivalence
open import fin
open import finite-commutative-semigroup
open import finset.instances
open import functions
open import semigroup

module _ {ℓD : Level} {D : Type ℓD} (CS : CommutativeSemigroupStr D) where
  open CommutativeSemigroupStr CS

  opaque
    finite⁺Merge-Fin1 : (f : (Fin 1) -> D) -> finite⁺Merge CS f == f zero-fin
    finite⁺Merge-Fin1 f = finite⁺Merge-eval CS (idEquiv _) f

    finite⁺Merge-Fin : {n : Nat} (f : Fin (suc (suc n)) -> D) ->
      finite⁺Merge CS f ==
      f zero-fin ∙ finite⁺Merge CS (f ∘ suc-fin)
    finite⁺Merge-Fin f =
      finite⁺Merge-eval CS (idEquiv _) f >=>
      ∙-right (sym (finite⁺Merge-eval CS (idEquiv _) (f ∘ suc-fin)))
