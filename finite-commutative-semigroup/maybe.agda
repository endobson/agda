{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-semigroup.maybe where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-semigroup
open import finite-commutative-semigroup.fin
open import finset.inhabited
open import finset.instances
open import functions
open import funext
open import maybe
open import semigroup
open import truncation
open import type-algebra

module _ {ℓD : Level} {D : Type ℓD} (CS : CommutativeSemigroupStr D) where
  open CommutativeSemigroupStr CS

  module _ {ℓA : Level} {A : Type ℓA} {{FA : Fin⁺SetStr A}} where
    opaque
      finite⁺Merge-Maybe : (f : Maybe A -> D) ->
        finite⁺Merge CS f == f nothing ∙ finite⁺Merge CS (f ∘ just)
      finite⁺Merge-Maybe f =
        unsquash (isSet-Domain _ _) (∥-map path (snd (Fin⁺Set-eq (get-Fin⁺Setⁱ A))))
        where
        module _ {n : Nat} (eq : A ≃ Fin (suc n)) where
          meq' : (Fin (suc (suc n))) ≃ Maybe A
          meq' = (Fin-Maybe-eq (suc n)) >eq> (equiv⁻¹ (Maybe-eq eq))

          path : finite⁺Merge CS f == f nothing ∙ finite⁺Merge CS (f ∘ just)
          path =
            finite⁺Merge-convert CS meq' f >=>
            finite⁺Merge-Fin CS (f ∘ eqFun meq') >=>
            ∙-right (cong (finite⁺Merge CS) (funExt (\_ ->
                       cong (f ∘ just ∘ eqInv eq) (fin-i-path refl))) >=>
                     sym (finite⁺Merge-convert CS (equiv⁻¹ eq) (f ∘ just)))
