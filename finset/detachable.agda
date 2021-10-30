{-# OPTIONS --cubical --safe --exact-split #-}

module finset.detachable where

open import base
open import cubical
open import equivalence
open import isomorphism
open import relation
open import fin
open import finset
open import finset.instances
open import finsum
open import fin-algebra
open import functions
open import sigma
open import subset
open import sum
open import truncation
open import type-algebra

private
  isFinSet-Detachable-Fin-zero :
    {ℓB : Level} (B : Subtype (Fin 0) ℓB) -> Detachable B -> isFinSet (Σ (Fin 0) (fst ∘ B))
  isFinSet-Detachable-Fin-zero _ _ = isFinSet-Uninhabited (¬fin-zero ∘ fst)


  isFinSet-Detachable-Fin-suc :
    {ℓB : Level} {n : Nat} (B : Subtype (Fin (suc n)) ℓB) ->
    Detachable B -> isFinSet (Σ (Fin n) (fst ∘ B ∘ suc-fin)) -> isFinSet (Σ (Fin (suc n)) (fst ∘ B))
  isFinSet-Detachable-Fin-suc {n = n1} B decide-B' = ∥-map handle
    where
    B' = fst ∘ B
    isProp-B' = snd ∘ B


    handle : Σ[ n2 ∈ Nat ] (Σ (Fin n1) (B' ∘ suc-fin) ≃ Fin n2) ->
             Σ[ n2 ∈ Nat ] (Σ (Fin (suc n1)) B' ≃ Fin n2)
    handle (n2 , eq) = bzero-case (decide-B' zero-fin)
     where

     bzero-case : Dec (B' zero-fin) -> Σ[ n2 ∈ Nat ] (Σ (Fin (suc n1)) B' ≃ Fin n2)
     bzero-case (yes b0) =
       suc n2 , (ΣFin-suc-eq' n1 B' >eq> ⊎-equiv (Contr-Top-eq isContr-B0) eq >eq>
                 (equiv⁻¹ (Fin-suc-⊎-eq n2)))
       where
       isContr-B0 : isContr (B' zero-fin)
       isContr-B0 = b0 , isProp-B' _ b0
     bzero-case (no ¬b) =
       n2 , (ΣFin-suc-eq' n1 B' >eq> ⊎-equiv (¬-Bot-eq ¬b) eq >eq> ⊎-Bot-eq _)

  isFinSet-Detachable-Fin :
    {ℓB : Level} {n : Nat} (B : Subtype (Fin n) ℓB) -> Detachable B -> isFinSet (Σ (Fin n) (fst ∘ B))
  isFinSet-Detachable-Fin {n = zero}  B decide-B = isFinSet-Detachable-Fin-zero B decide-B
  isFinSet-Detachable-Fin {n = suc n} B decide-B =
    isFinSet-Detachable-Fin-suc B decide-B (isFinSet-Detachable-Fin B' decide-B')
    where
    B' : Subtype (Fin n) _
    B' = B ∘ suc-fin
    decide-B' : Detachable B'
    decide-B' = decide-B ∘ suc-fin

abstract
  isFinSet-Detachable : {ℓA ℓB : Level} {A : Type ℓA} (B : Subtype A ℓB) ->
                        isFinSet A -> Detachable B -> isFinSet (∈-Subtype B)
  isFinSet-Detachable {ℓB = ℓB} {A = A} B fs-A d-B = ∥-bind handle fs-A
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> isFinSet (∈-Subtype B)
    handle (n , eq) = ∥-bind handle2 (isFinSet-Detachable-Fin B' d-B')
      where
      eq' : Fin n ≃ A
      eq' = equiv⁻¹ eq
      B' : Subtype (Fin n) ℓB
      B' i = B (eqFun eq' i)
      d-B' : Detachable B'
      d-B' = d-B ∘ (eqFun eq')
      handle2 : Σ[ n2 ∈ Nat ] ((∈-Subtype B') ≃ Fin n2) -> isFinSet (∈-Subtype B)
      handle2 (n2 , eq2) = ∣ n2 , reindexΣ eq' (fst ∘ B) >eq> eq2 ∣

  isFinSet-DetachableComp : {ℓA ℓB : Level} {A : Type ℓA} (B : Subtype A ℓB) ->
                            isFinSet A -> Detachable B -> isFinSet (∉-Subtype B)
  isFinSet-DetachableComp B fs-A d-B =
    isFinSet-Detachable (Subtype-Comp B) fs-A (Detachable-Comp B d-B)

FinSet-Detachable : {ℓA ℓS : Level} -> (FA : FinSet ℓA) -> (S : Subtype ⟨ FA ⟩ ℓS) -> Detachable S ->
                    FinSet (ℓ-max ℓA ℓS)
FinSet-Detachable FA S d-S = (∈-Subtype S) , isFinSet-Detachable S (snd FA) d-S

FinSet-DetachableComp : {ℓA ℓS : Level} -> (FA : FinSet ℓA) -> (S : Subtype ⟨ FA ⟩ ℓS) -> Detachable S ->
                        FinSet (ℓ-max ℓA ℓS)
FinSet-DetachableComp FA S d-S = (∉-Subtype S) , isFinSet-DetachableComp S (snd FA) d-S
