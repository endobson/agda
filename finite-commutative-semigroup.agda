{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module finite-commutative-semigroup where

open import base
open import equality
open import equivalence
open import fin
open import finset
open import finset.inhabited
open import functions
open import funext
open import hlevel
open import permutation.swap
open import semigroup
open import truncation

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {D : Type ℓ} (CS : CommutativeSemigroupStr D) where
  open CommutativeSemigroupStr CS

  private
    finMergeDep : (n : Nat) -> (f : (Fin (suc n)) -> D) -> D
    finMergeDep zero    f = f zero-fin
    finMergeDep (suc n) f = f zero-fin ∙ (finMergeDep n (f ∘ suc-fin))

    enumerationMerge : {n : Nat} -> (Fin (suc n) -> A) -> (A -> D) -> D
    enumerationMerge enum f = finMergeDep _ (f ∘ enum)

    equivMerge : {n : Nat} -> (A ≃ Fin (suc n)) -> (A -> D) -> D
    equivMerge eq f = enumerationMerge (eqInv eq) f

    equivMerge' : (n : Nat) -> (A -> D) -> (A ≃ Fin (suc n)) -> D
    equivMerge' _ f eq = enumerationMerge (eqInv eq) f

    opaque
      encode-swap-suc-fin : {n : Nat} (sw : Swap n)
                            -> encode-swap (swap-skip sw) ∘ suc-fin == suc-fin ∘ (encode-swap sw)
      encode-swap-suc-fin sw =
        cong (_∘ suc-fin ) (encode-swap-swap-skip sw)
        >=> (fin-rec-suc zero-fin (suc-fin ∘ encode-swap sw))

      finMergeDep-swap : {n : Nat} -> (sw : Swap (suc n)) -> (f : (Fin (suc n)) -> D) ->
                         finMergeDep n f == finMergeDep n (f ∘ encode-swap sw)
      finMergeDep-swap {n = (suc n)} (swap-skip sw) f =
        ∙-right (finMergeDep-swap sw (f ∘ suc-fin)) >=>
        cong (\i -> (f zero-fin ∙ (finMergeDep n (f ∘ i))))
             (sym (encode-swap-suc-fin sw))
      finMergeDep-swap {n = (suc (suc n))} swap f =
        sym ∙-assoc >=> ∙-left ∙-commute >=> ∙-assoc
      finMergeDep-swap {n = (suc zero)} swap f =
        ∙-commute >=> cong2 _∙_ (cong f (fin-i-path refl)) (cong f (fin-i-path refl))

      finMergeDep-sperm : {n : Nat} -> (s : SwapPerm (suc n)) -> (f : (Fin (suc n)) -> D) ->
                          finMergeDep n f == finMergeDep n (f ∘ encode-sperm s)
      finMergeDep-sperm {n} (l , s) = finMergeDep-sperm' l s
        where
        finMergeDep-sperm' : (l : Nat) (s : SwapPerm' (suc n) l) -> (f : (Fin (suc n)) -> D) ->
                             finMergeDep n f == finMergeDep n (f ∘ encode-sperm' l s)
        finMergeDep-sperm' zero _ f = refl
        finMergeDep-sperm' (suc l) swaps f =
          finMergeDep-swap (swaps zero-fin) f >=>
          (finMergeDep-sperm' l (swaps ∘ suc-fin) (f ∘ (encode-swap (swaps zero-fin))))

      finMergeDep-inj : {n : Nat} -> (s : Fin (suc n) -> Fin (suc n)) -> Injective s ->
                        (f : (Fin (suc n)) -> D) ->
                        finMergeDep n f == finMergeDep n (f ∘ s)
      finMergeDep-inj {n} s inj-s f =
        finMergeDep-sperm (fst Σswaps) f >=>
        cong (finMergeDep n) (cong (f ∘_) (snd Σswaps))
        where
        Σswaps : Σ[ sp ∈ SwapPerm (suc n) ] (encode-sperm sp == s)
        Σswaps = fininj-sperm-path (s , inj-s)


    equivMerge'-constant : (n : Nat) -> (f : (A -> D)) -> 2-Constant (equivMerge' n f)
    equivMerge'-constant n f eq1 eq2 =
      ans1 >=> cong (\e -> enumerationMerge e f) enum-path
      where

      reindex : Fin (suc n) -> Fin (suc n)
      reindex = eqFun eq1 ∘ eqInv eq2

      reindex-inj : Injective reindex
      reindex-inj {x} {y} p = path2
        where
        path1 : (eqInv eq2 x) == (eqInv eq2 y)
        path1 =
          sym (eqRet eq1 (eqInv eq2 x))
          >=> cong (eqInv eq1) p
          >=> (eqRet eq1 (eqInv eq2 y))
        path2 : x == y
        path2 =
          sym (eqSec eq2 x)
          >=> cong (eqFun eq2) path1
          >=> (eqSec eq2 y)

      enum-path : (eqInv eq1 ∘ reindex) == eqInv eq2
      enum-path = funExt (\_ -> eqRet eq1 _)

      ans1 : enumerationMerge (eqInv eq1) f == enumerationMerge (eqInv eq1 ∘ reindex) f
      ans1 = finMergeDep-inj reindex reindex-inj (f ∘ (eqInv eq1))

  opaque
    finite⁺Mergeᵉ : {ℓ : Level} -> (S : Fin⁺Set ℓ) -> (⟨ S ⟩ -> D) -> D
    finite⁺Mergeᵉ S f =
      ∥->Set isSet-Domain (equivMerge' _ f) (equivMerge'-constant _ f)
                          (snd (Fin⁺Set-eq S))

  finite⁺Merge : {ℓ : Level} {I : Type ℓ} {{FI : Fin⁺SetStr I}} -> (I -> D) -> D
  finite⁺Merge {I = I} = finite⁺Mergeᵉ (get-Fin⁺Setⁱ I)

  opaque
    unfolding finite⁺Mergeᵉ

    finite⁺Mergeᵉ-eval : {ℓ : Level} (A : Fin⁺Set ℓ) {n : Nat}
                         -> (eq : (⟨ A ⟩ ≃ Fin (suc n))) -> (f : ⟨ A ⟩ -> D)
                         -> finite⁺Mergeᵉ A f == equivMerge eq f
    finite⁺Mergeᵉ-eval {ℓ} (A , isFinA , ∣a∣) {n} eq f =
      \i -> finite⁺Mergeᵉ (A , (squash isFinA ∣ suc n , eq ∣ i) ,
                               (squash ∣a∣ ∣ eqInv eq zero-fin ∣ i)) f

    finite⁺Merge-eval : {ℓ : Level} {A : Type ℓ} {{FA : Fin⁺SetStr A}} {n : Nat} ->
                        (eq : A ≃ Fin (suc n)) -> (f : A -> D) ->
                        finite⁺Merge f == equivMerge eq f
    finite⁺Merge-eval {A = A} = finite⁺Mergeᵉ-eval (get-Fin⁺Setⁱ A)

  opaque
    finite⁺Mergeᵉ-convert : {ℓ₁ ℓ₂ : Level} -> (A : Fin⁺Set ℓ₁) (B : Fin⁺Set ℓ₂)
                            (eq : (⟨ B ⟩ ≃ ⟨ A ⟩) ) (f : ⟨ A ⟩ -> D) ->
                            finite⁺Mergeᵉ A f == finite⁺Mergeᵉ B (f ∘ (eqFun eq))
    finite⁺Mergeᵉ-convert A B eq f =
      unsquash (isSet-Domain _ _) (∥-map path (snd (Fin⁺Set-eq A)))
      where
      module _ {n : Nat} (eqA : ⟨ A ⟩ ≃ Fin (suc n)) where
        eqB : ⟨ B ⟩ ≃ Fin (suc n)
        eqB = eq >eq> eqA

        path : finite⁺Mergeᵉ A f == finite⁺Mergeᵉ B (f ∘ (eqFun eq))
        path = finite⁺Mergeᵉ-eval A eqA f >=>
               cong (finMergeDep n) (funExt (\_ -> cong f (sym (eqSec eq _)))) >=>
               sym (finite⁺Mergeᵉ-eval B eqB (f ∘ (eqFun eq)))

    finite⁺Merge-convert : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} ->
                           {{FA : Fin⁺SetStr A}} {{FB : Fin⁺SetStr B}}
                           (eq : (B ≃ A) ) (f : A -> D) ->
                           finite⁺Merge f == finite⁺Merge (f ∘ (eqFun eq))
    finite⁺Merge-convert = finite⁺Mergeᵉ-convert (get-Fin⁺Setⁱ _) (get-Fin⁺Setⁱ _)
