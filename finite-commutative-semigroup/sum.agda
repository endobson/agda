{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-semigroup.sum where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-semigroup
open import finite-commutative-semigroup.fin
open import finite-commutative-semigroup.maybe
open import finset.inhabited
open import finset.instances
open import finset.instances.sum
open import functions
open import funext
open import maybe
open import semigroup
open import sum
open import truncation
open import type-algebra

module _ {ℓD : Level} {D : Type ℓD} (CS : CommutativeSemigroupStr D) where
  open CommutativeSemigroupStr CS

  private
    module _ {ℓB : Level} {B : Type ℓB} {{FB : Fin⁺SetStr B}} where
      finite⁺Merge-sum-fin :
        (n : Nat) (f : Fin (suc n) -> D) (g : B -> D) ->
        finite⁺Merge CS (either f g) ==
        finite⁺Merge CS f ∙ finite⁺Merge CS g
      finite⁺Merge-sum-fin zero f g =
        finite⁺Merge-convert CS (equiv⁻¹ eq) (either f g) >=>
        finite⁺Merge-Maybe CS (either f g ∘ eqInv eq) >=>
        ∙-left (sym (finite⁺Merge-Fin1 CS f))
        where
        eq : (Fin 1 ⊎ B) ≃ Maybe B
        eq = (⊎-equiv Fin-Top-eq (idEquiv B)) >eq> ⊎-Top-eq
      finite⁺Merge-sum-fin (suc n) f g =
        path1 >=>
        finite⁺Merge-Maybe CS _ >=>
        (∙-right (path2 >=> path3)) >=>
        sym ∙-assoc >=>
        ∙-left (sym (finite⁺Merge-Fin CS f))
        where
        eq : (Fin (suc (suc n)) ⊎ B) ≃ Maybe (Fin (suc n) ⊎ B)
        eq = ⊎-equiv (Fin-Maybe-eq (suc n)) (idEquiv B) >eq> ⊎-left-Maybe-eq

        path1 : finite⁺Merge CS (either f g) ==
                finite⁺Merge CS (either f g ∘ eqInv eq)
        path1 = finite⁺Merge-convert CS (equiv⁻¹ eq) (either f g)
        path2 : finite⁺Merge CS (either f g ∘ eqInv eq ∘ just) ==
                finite⁺Merge CS (either (f ∘ suc-fin) g)
        path2 = cong (finite⁺Merge CS) (funExt (\{ (inj-l _) -> refl ; (inj-r _) -> refl }))
        path3 : finite⁺Merge CS (either (f ∘ suc-fin) g) ==
                finite⁺Merge CS (f ∘ suc-fin) ∙ finite⁺Merge CS g
        path3 = finite⁺Merge-sum-fin n (f ∘ suc-fin) g

  module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
           {{FA : Fin⁺SetStr A}} {{FB : Fin⁺SetStr B}} where
    private
      finite⁺Merge-⊎' :
        (f : A -> D) (g : B -> D) ->
        finite⁺Merge CS (either f g) ==
        finite⁺Merge CS f ∙ finite⁺Merge CS g
      finite⁺Merge-⊎' f g =
        unsquash (isSet-Domain _ _) (∥-map path (snd (Fin⁺Set-eq (get-Fin⁺Setⁱ A))))
        where
        module _ {n : Nat} (eq : A ≃ Fin (suc n)) where
          path1 : finite⁺Merge CS (either f g) ==
                  finite⁺Merge CS (either f g ∘ eqInv (⊎-equiv eq (idEquiv B)))
          path1 = finite⁺Merge-convert CS (equiv⁻¹ (⊎-equiv eq (idEquiv B))) (either f g)

          path2 : (either f g ∘ eqInv (⊎-equiv eq (idEquiv B))) ==
                  (either (f ∘ eqInv eq) g)
          path2 = funExt (\{ (inj-l _) -> refl ; (inj-r _) -> refl })

          path3 : finite⁺Merge CS (either (f ∘ eqInv eq) g) ==
                  finite⁺Merge CS (f ∘ eqInv eq) ∙ finite⁺Merge CS g
          path3 = finite⁺Merge-sum-fin n _ _

          path4 : finite⁺Merge CS f ==
                  finite⁺Merge CS (f ∘ eqInv eq)
          path4 = finite⁺Merge-convert CS (equiv⁻¹ eq) f

          path : finite⁺Merge CS (either f g) ==
                 finite⁺Merge CS f ∙ finite⁺Merge CS g
          path = path1 >=> cong (finite⁺Merge CS) path2 >=> path3 >=> ∙-left (sym path4)

    opaque
      finite⁺Merge-⊎ :
        (f : (A ⊎ B) -> D) ->
        finite⁺Merge CS f ==
        finite⁺Merge CS (f ∘ inj-l) ∙ finite⁺Merge CS (f ∘ inj-r)
      finite⁺Merge-⊎ f =
        cong (finite⁺Merge CS) (funExt (\{ (inj-l _) -> refl ; (inj-r _) -> refl })) >=>
        finite⁺Merge-⊎' (f ∘ inj-l) (f ∘ inj-r)
