{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-semigroup.property where

open import base
open import equality-path
open import equivalence
open import fin
open import finite-commutative-semigroup
open import finite-commutative-semigroup.fin
open import finset.inhabited
open import finset.instances
open import functions
open import hlevel
open import nat.order
open import semigroup
open import truncation

module _ {ℓD : Level} {D : Type ℓD} (CS : CommutativeSemigroupStr D) where
  open CommutativeSemigroupStr CS

  module _ {ℓP : Level} {P : D -> Type ℓP} (isProp-P : (d : D) -> isProp (P d)) where
    private
      finite⁺Merge-some-fin :
        (n : Nat) (f : Fin (suc n) -> D) (i : Fin (suc n)) ->
        (P (f i)) ->
        (∀ d₁ d₂ -> P d₁ -> P (d₁ ∙ d₂)) ->
        P (finite⁺Merge CS f)
      finite⁺Merge-some-fin zero f i Pi _ =
        subst P (cong f pi >=> sym (finite⁺Merge-Fin1 CS f)) Pi
        where
        pi : i == zero-fin
        pi = sym (snd isContrFin1 i)
      finite⁺Merge-some-fin (suc n) f (zero , lt) Pi m =
        subst P (sym (finite⁺Merge-Fin CS f))
          (m _ _ (subst P (cong f (fin-i-path refl)) Pi))
      finite⁺Merge-some-fin (suc n) f (suc i , lt) Pi m =
        subst P (∙-commute >=> sym (finite⁺Merge-Fin CS f)) (m _ _ rec)
        where
        i₂ : Fin (suc n)
        i₂ = i , pred-≤ lt
        Pi₂ : P (f (suc-fin i₂))
        Pi₂ = subst P (cong f (fin-i-path refl)) Pi
        rec : P (finite⁺Merge CS (f ∘ suc-fin))
        rec = finite⁺Merge-some-fin n (f ∘ suc-fin) i₂ Pi₂ m

    module _ {ℓI : Level} {I : Type ℓI} {{FI : Fin⁺SetStr I}} (f : I -> D)
      where
      opaque
        finite⁺Merge-somewhere :
          ∃[ i ∈ I ] (P (f i)) ->
          (∀ d₁ d₂ -> P d₁ -> P (d₁ ∙ d₂)) ->
          P (finite⁺Merge CS f)
        finite⁺Merge-somewhere ∃i m = unsquash (isProp-P _) (∥-map2 handle ∃i ∃eq)
          where
          ∃eq : ∃[ n ∈ Nat ] (I ≃ Fin (suc n))
          ∃eq = ∥-map (\eq -> _ , eq)  (snd (Fin⁺Set-eq (get-Fin⁺Setⁱ I)))
          handle : Σ[ i ∈ I ] (P (f i)) -> Σ[ n ∈ Nat ] (I ≃ Fin (suc n)) ->
                   P (finite⁺Merge CS f)
          handle (i , Pi) (n , eq) =
            subst P (sym (finite⁺Merge-convert CS (equiv⁻¹ eq) f)) ans
            where
            ans : P (finite⁺Merge CS (f ∘ eqInv eq))
            ans = finite⁺Merge-some-fin n _ (eqFun eq i) (subst P (cong f (sym (eqRet eq i))) Pi) m
