{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module finite-commutative-monoid where

open import base
open import commutative-monoid
open import cubical
open import equality
open import equivalence
open import fin
open import finset
open import functions
open import funext
open import isomorphism
open import nat.order
open import permutation.swap
open import truncation

open EqReasoning

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {D : Type ℓ} (CM : CommMonoid D) where
  open CommMonoid CM

  finMergeDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finMergeDep zero    _ = ε
  finMergeDep (suc n) f = f zero-fin ∙ (finMergeDep n (f ∘ suc-fin))

  enumerationMerge : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationMerge enum f = finMergeDep _ (f ∘ enum)

  equivMerge : {n : Nat} -> (A ≃ Fin n) -> (A -> D)  -> D
  equivMerge eq f = enumerationMerge (eqInv eq) f

  private
    encode-swap-suc-fin : {n : Nat} (sw : Swap n)
                          -> encode-swap (swap-skip sw) ∘ suc-fin == suc-fin ∘ (encode-swap sw)
    encode-swap-suc-fin sw =
      cong (_∘ suc-fin ) (encode-swap-swap-skip sw)
      >=> (fin-rec-suc zero-fin (suc-fin ∘ encode-swap sw))

    finMergeDep-swap : {n : Nat} -> (sw : Swap n) -> (f : (Fin n) -> D)
                       -> finMergeDep n f == finMergeDep n (f ∘ encode-swap sw)
    finMergeDep-swap {n = (suc n)} (swap-skip sw) f =
      cong (f zero-fin ∙_) (finMergeDep-swap sw (f ∘ suc-fin))
      >=> cong (\i -> (f zero-fin ∙ (finMergeDep n (f ∘ i))))
               (sym (encode-swap-suc-fin sw))
    finMergeDep-swap {n = (suc (suc n))} swap f = ans
      where
      ans1 : (f zero-fin ∙ f (suc-fin zero-fin)) ==
             (f (suc-fin zero-fin) ∙ (f zero-fin))
      ans1 = ∙-commute

      f2 : Fin n -> D
      f2 x = f (suc-fin (suc-fin x))

      ans : (f zero-fin ∙ (f (suc-fin zero-fin) ∙ finMergeDep n f2))
            == (f (suc-fin zero-fin) ∙ (f zero-fin ∙ finMergeDep n f2))
      ans = sym ∙-assoc >=> ∙-left ans1 >=> ∙-assoc

    finMergeDep-swapPerm' : {n : Nat} -> (l : Nat)
                            -> (sw : SwapPerm' n l) -> (f : (Fin n) -> D)
                            -> finMergeDep n f == finMergeDep n (f ∘ encode-sperm' l sw)
    finMergeDep-swapPerm' zero    sw f = refl
    finMergeDep-swapPerm' (suc l) sw f = ans
      where
      rec : finMergeDep _ (f ∘ encode-swap (sw zero-fin)) ==
            finMergeDep _ (f ∘ encode-swap (sw zero-fin) ∘ encode-sperm' l (sw ∘ suc-fin))
      rec = finMergeDep-swapPerm' l (sw ∘ suc-fin) (f ∘ encode-swap (sw zero-fin))

      ans : finMergeDep _ f ==
            finMergeDep _ (f ∘ encode-swap (sw zero-fin) ∘ encode-sperm' l (sw ∘ suc-fin))
      ans = finMergeDep-swap (sw zero-fin) f >=> rec

    finMergeDep-swapPerm : {n : Nat}
                           -> (sw : SwapPerm n) -> (f : (Fin n) -> D)
                           -> finMergeDep n f == finMergeDep n (f ∘ encode-sperm sw)
    finMergeDep-swapPerm (l , sw) = finMergeDep-swapPerm' l sw


    enumerationMerge-swapPerm :
      {n : Nat} -> (sw : SwapPerm n) -> (f : A -> D) -> (enum : (Fin n -> A))
      -> enumerationMerge enum f == enumerationMerge (enum ∘ encode-sperm sw) f
    enumerationMerge-swapPerm sw f enum = finMergeDep-swapPerm sw (f ∘ enum)


    equivMerge' : {n : Nat} -> (A -> D) -> (A ≃ Fin n) -> D
    equivMerge' f eq = enumerationMerge (eqInv eq) f


  private
    equivMerge'-constant : {n : Nat} -> (f : (A -> D)) -> 2-Constant (equivMerge' {n = n} f)
    equivMerge'-constant {n = n} f eq1 eq2 = ans
      where

      reindex : Fin n -> Fin n
      reindex = eqFun eq1 ∘ eqInv eq2

      reindex-inj : isInjective reindex
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

      reindex-point : (i : Fin n) -> (eqInv eq1 (reindex i)) == (eqInv eq2 i)
      reindex-point i = eqRet eq1 (eqInv eq2 i)

      reindex-path : eqInv eq1 ∘ reindex == eqInv eq2
      reindex-path k i = reindex-point i k

      Σswaps = fininj-sperm-path (reindex , reindex-inj)
      swaps : SwapPerm n
      swaps = fst Σswaps
      reindex-swap-path : (encode-sperm swaps) == reindex
      reindex-swap-path = snd Σswaps

      ans2 : enumerationMerge (eqInv eq1) f == enumerationMerge (eqInv eq1 ∘ reindex) f
      ans2 = enumerationMerge-swapPerm swaps f (eqInv eq1)
             >=> (\k -> enumerationMerge (eqInv eq1 ∘ reindex-swap-path k) f)


      ans : enumerationMerge (eqInv eq1) f == enumerationMerge (eqInv eq2) f
      ans = ans2 >=> (\i -> enumerationMerge (reindex-path i) f)



  -- module _ where
  abstract
    finiteMergeᵉ : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
    finiteMergeᵉ (S , ∣n,eq∣) f =
      ∥->Set isSet-Domain (equivMerge' f) (equivMerge'-constant f)
                          (snd (isFinSet->isFinSetΣ ∣n,eq∣))

  finiteMerge : {ℓ : Level} {I : Type ℓ} {{FI : FinSetStr I}} -> (I -> D) -> D
  finiteMerge {I = I} {{FI = FI}} = finiteMergeᵉ (I , FinSetStr.isFin FI)


  abstract

    finiteMergeᵉ-eval : {ℓ : Level} (A : FinSet ℓ) {n : Nat}
                       -> (eq : (⟨ A ⟩ ≃ Fin n)) -> (f : ⟨ A ⟩ -> D)
                       -> finiteMergeᵉ A f == equivMerge eq f
    finiteMergeᵉ-eval {ℓ} (A , isFinA) {n} eq f =
      begin
        finiteMergeᵉ (A , isFinA) f
      ==< (\i -> finiteMergeᵉ (A , squash isFinA ∣ n , eq ∣ i) f)>
        finiteMergeᵉ (A , ∣ n , eq ∣) f
      end

    finiteMerge-eval : {ℓ : Level} {A : Type ℓ} {{FA : FinSetStr A}} {n : Nat} ->
                       (eq : A ≃ Fin n) -> (f : A -> D) ->
                       finiteMerge f == equivMerge eq f
    finiteMerge-eval {A = A} {{FA = FA}} = finiteMergeᵉ-eval (A , FinSetStr.isFin FA)


    finiteMergeᵉ-convert : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                           (eq : (⟨ B ⟩ ≃ ⟨ A ⟩) ) (f : ⟨ A ⟩ -> D)
                           -> finiteMergeᵉ A f == finiteMergeᵉ B (f ∘ (eqFun eq))
    finiteMergeᵉ-convert {ℓ₁} {ℓ₂} A B eq f = outer-path
      where
      module _ where
        A' = ⟨ A ⟩
        isFinA = snd A
        B' = ⟨ B ⟩
        isFinB = snd B

      inner-path : Σ[ n ∈ Nat ] (A' ≃ Fin n)
                   -> finiteMergeᵉ A f == finiteMergeᵉ B (f ∘ (eqFun eq))
      inner-path (n , eqA) =
        begin
          finiteMergeᵉ A f
        ==< finiteMergeᵉ-eval A eqA f >
          equivMerge eqA f
        ==<>
          finMergeDep n (f ∘ eqInv eqA)
        ==< (\i -> finMergeDep n (f ∘ eqPath i)) >
          finMergeDep n (f ∘ (eqFun eq) ∘ (eqInv eq) ∘ (eqInv eqA))
        ==<>
          finMergeDep n (f ∘ (eqFun eq) ∘ (eqInv eqB))
        ==<>
          equivMerge eqB (f ∘ (eqFun eq))
        ==< sym (finiteMergeᵉ-eval B eqB (f ∘ (eqFun eq))) >
          finiteMergeᵉ B (f ∘ (eqFun eq))
        end
        where

        eqB : B' ≃ Fin n
        eqB = ∘-equiv eqA eq

        eqPath : eqInv eqA == (eqFun eq) ∘ (eqInv eq) ∘ (eqInv eqA)
        eqPath = sym (funExt (\x -> eqSec eq (eqInv eqA x)))


      outer-path : finiteMergeᵉ A f == finiteMergeᵉ B (f ∘ (eqFun eq))
      outer-path = unsquash (isSet-Domain _ _) (∥-map inner-path isFinA)

    finiteMerge-convert : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
                          {{FA : FinSetStr A}} {{FB : FinSetStr B}} ->
                          (eq : B ≃ A) (f : A -> D) ->
                          finiteMerge f == finiteMerge (f ∘ (eqFun eq))
    finiteMerge-convert {A = A} {B = B} {{FA = FA}} {{FB = FB}} =
      finiteMergeᵉ-convert (A , FinSetStr.isFin FA) (B , FinSetStr.isFin FB)

    finiteMergeᵉ-convert-iso : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                               (i : Iso ⟨ B ⟩ ⟨ A ⟩) (f : ⟨ A ⟩ -> D)
                               -> finiteMergeᵉ A f == finiteMergeᵉ B (f ∘ (Iso.fun i))
    finiteMergeᵉ-convert-iso {ℓ₁} {ℓ₂} A B i f = finiteMergeᵉ-convert A B (isoToEquiv i) f

    finiteMerge-convert-iso : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
                              {{FA : FinSetStr A}} {{FB : FinSetStr B}} ->
                              (i : Iso B A) (f : A -> D) ->
                              finiteMerge f == finiteMerge (f ∘ (Iso.fun i))
    finiteMerge-convert-iso {A = A} {B = B} {{FA = FA}} {{FB = FB}} =
      finiteMergeᵉ-convert-iso (A , FinSetStr.isFin FA) (B , FinSetStr.isFin FB)
