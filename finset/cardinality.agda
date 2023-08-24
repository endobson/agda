{-# OPTIONS --cubical --safe --exact-split #-}

module finset.cardinality where

open import base
open import cubical
open import equality
open import equivalence
open import isomorphism
open import fin
open import finset
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import truncation

private
  variable
    ℓ : Level


private
  uninhabited-cardinality0⁻ : (A : FinSet ℓ) -> cardinality A == 0 -> ¬ ⟨ A ⟩
  uninhabited-cardinality0⁻ (A , fsA) p a =
    unsquash isPropBot
      (∥-map (\{ eq -> (¬fin-zero (subst Fin p (eqFun eq a)))})
             (snd (isFinSet->isFinSetΣ fsA)))


  inhabited-0<cardinality⁺ : (A : FinSet ℓ) -> ∥ ⟨ A ⟩  ∥ -> 0 < cardinality A
  inhabited-0<cardinality⁺ A a =
    case (split-< (cardinality A) 1) of (\{
      (inj-r 1≤ca) -> 1≤ca ;
      (inj-l sca≤1) -> bot-elim (zero-case (zero-≤->zero (pred-≤ sca≤1))) })
    where
    zero-case : ¬ (cardinality A == 0)
    zero-case cA=0 =
      unsquash isPropBot (∥-map (uninhabited-cardinality0⁻ A cA=0) a)


  inhabited-0<cardinality⁻ : (A : FinSet ℓ) -> 0 < cardinality A -> ∥ ⟨ A ⟩  ∥
  inhabited-0<cardinality⁻ A 0<cA = ∥-map (f refl) (snd (isFinSet->isFinSetΣ (snd A)))
    where
    f : {n : Nat} -> cardinality A == n -> ⟨ A ⟩ ≃ Fin n -> ⟨ A ⟩
    f {n = zero} cA=0 eq = bot-elim (irrefl-< (trans-<-= 0<cA cA=0))
    f {n = suc n} cA=sn eq = eqInv eq (0 , suc-≤ zero-≤)


  uninhabited-cardinality0⁺ : (A : FinSet ℓ) -> ¬ ⟨ A ⟩ -> cardinality A == 0
  uninhabited-cardinality0⁺ A ¬a =
    case (split-< 0 (cardinality A)) of (\{
      (inj-r ca≤0) -> (zero-≤->zero ca≤0) ;
      (inj-l 0<ca) ->
        bot-elim (unsquash isPropBot (∥-map ¬a (inhabited-0<cardinality⁻ A 0<ca)))})

uninhabited-cardinality0 : (A : FinSet ℓ) -> ¬ ⟨ A ⟩ ≃ (cardinality A == 0)
uninhabited-cardinality0 A =
  isoToEquiv (isProp->iso (uninhabited-cardinality0⁺ A)  (uninhabited-cardinality0⁻ A)
                          (isProp¬ _) (isSetNat _ _))

inhabited-0<cardinality : (A : FinSet ℓ) -> ∥ ⟨ A ⟩ ∥ ≃ (0 < cardinality A)
inhabited-0<cardinality A =
  isoToEquiv (isProp->iso (inhabited-0<cardinality⁺ A) (inhabited-0<cardinality⁻ A)
                          squash isProp-<)
