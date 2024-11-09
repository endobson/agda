{-# OPTIONS --cubical --safe --exact-split #-}

module finset.subset where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import finset
open import finset.instances
open import finset.instances.base
open import functions
open import hlevel
open import isomorphism
open import maybe
open import nat
open import nat.order
open import nat.bounded
open import order
open import order.instances.nat
open import relation
open import sigma.base
open import sum
open import truncation
open import type-algebra
open import univalence

private
  variable
    ℓ : Level

private
  ΣFin-suc-eq : (n : Nat) (P : Pred Nat ℓ) ->
                (Σ[ i ∈ Fin (suc n) ] ∥ P (Fin.i i) ∥) ≃ (∥ P n ∥ ⊎  Σ[ i ∈ Fin n ] ∥ P (Fin.i i) ∥)
  ΣFin-suc-eq n P = (isoToEquiv i)
    where
    P' : {n : Nat} -> Fin n -> Type _
    P' = P ∘ Fin.i

    handle : (j : Fin (suc n)) -> Dec (Fin.i j == n) -> ∥ P' j ∥ ->
             (∥ P n ∥ ⊎  Σ[ i ∈ Fin n ] ∥ P' i ∥)
    handle _        (yes path  ) p = inj-l (subst (\x -> ∥ P x ∥) path p)
    handle (j , lt) (no no-path) p = inj-r ((j , lt2) , p)
      where
      lt2 : j < n
      lt2 = strengthen-≤ (pred-≤ lt) no-path

    forward : (Σ[ i ∈ Fin (suc n) ] ∥ P' i ∥) -> (∥ P n ∥ ⊎  Σ[ i ∈ Fin n ] ∥ P' i ∥)
    forward (j , p) = handle j (decide-nat (Fin.i j) n) p

    backward : (∥ P n ∥ ⊎  Σ[ i ∈ Fin n ] ∥ P' i ∥) -> (Σ[ i ∈ Fin (suc n) ] ∥ P' i ∥)
    backward (inj-l p)              = (n , add1-< n), p
    backward (inj-r ((j , lt) , p)) = (j , right-suc-< lt) , p

    forward-yes : {jp : (Σ[ i ∈ Fin (suc n) ] ∥ P' i ∥)} -> (path : Fin.i ⟨ jp ⟩ == n) ->
                  forward jp == inj-l (subst (\x -> ∥ P x ∥) path (snd jp))
    forward-yes {j , p} path with (decide-nat (Fin.i j) n)
    ... | (yes path2) = (\i -> inj-l (subst (\x -> ∥ P x ∥) (pp i) p))
      where
      pp : path2 == path
      pp = (isSetNat (Fin.i j) n path2 path)
    ... | (no no-path) = bot-elim (no-path path)

    forward-no : {jp : (Σ[ i ∈ Fin (suc n) ] ∥ P' i ∥)} -> (no-path : Fin.i ⟨ jp ⟩ != n) ->
                  forward jp == inj-r (((Fin.i (fst jp)) ,
                                        strengthen-≤ (pred-≤ (Fin.i<n (fst jp))) no-path) , (snd jp))
    forward-no {j , p} no-path with (decide-nat (Fin.i j) n)
    ... | (no no-path2) = (\i -> inj-r (((Fin.i j) ,
                                        strengthen-≤ (pred-≤ (Fin.i<n j)) (np i)) , p))
      where
      np : no-path2 == no-path
      np = isProp¬ _ _ _
    ... | (yes path) = bot-elim (no-path path)

    open Iso
    i : Iso (Σ[ i ∈ Fin (suc n) ] ∥ P' i ∥) (∥ P n ∥ ⊎  Σ[ i ∈ Fin n ] ∥ P' i ∥)
    i .fun jp = forward jp
    i .inv x = backward x
    i .rightInv (inj-l p) = forward-yes refl >=> cong inj-l (squash _ _)
    i .rightInv (inj-r ((j , lt) , p)) =
      forward-no (<->!= lt) >=> cong inj-r (ΣProp-path squash (fin-i-path refl))
    i .leftInv (j , p) = (ΣProp-path squash (fin-i-path (handle'2 (decide-nat (Fin.i j) n))))
      where
      handle'2 : Dec (Fin.i j == n) -> Fin.i (fst (backward (forward (j , p)))) == Fin.i j
      handle'2 (yes path) = cong (Fin.i ∘ fst ∘ backward) (forward-yes path) >=> (sym path)
      handle'2 (no no-path) = cong (Fin.i ∘ fst ∘ backward) (forward-no no-path)


  decidableSubset->isFinSet : {P : Pred Nat ℓ} -> Decidable P ->
                              (n : Nat) -> isFinSet (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥ )
  decidableSubset->isFinSet {P = P} decP zero = isFinSet-Uninhabited empty
    where
    empty : ¬(Σ[ i ∈ Fin 0 ] ∥ P (Fin.i i) ∥)
    empty (i , _) = ¬fin-zero i

  decidableSubset->isFinSet {ℓ} {P = P} decP (suc n) = handle (decP n)
    where
    rec : isFinSet (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥ )
    rec = decidableSubset->isFinSet decP n

    path : (Σ[ i ∈ (Fin (suc n)) ] ∥ P (Fin.i i) ∥) ==
           (∥ P n ∥ ⊎ (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥))
    path = ua (ΣFin-suc-eq n P)


    handle : Dec (P n) -> isFinSet (Σ[ i ∈ (Fin (suc n)) ] ∥ P (Fin.i i) ∥ )
    handle (yes p) = subst isFinSet (sym path2) (isFinSet-Maybe rec)
      where
      path2 : (Σ[ i ∈ (Fin (suc n)) ] ∥ P (Fin.i i) ∥) ==
              Maybe (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥)
      path2 = path
              >=> (\i -> (∥-Top p i) ⊎ (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥))
              >=> ua (⊎-equiv (liftEquiv _ _) (idEquiv _))
              >=> ua ⊎-Top-eq

    handle (no ¬p) = subst isFinSet (sym path2) rec
      where
      path2 : (Σ[ i ∈ (Fin (suc n)) ] ∥ P (Fin.i i) ∥) ==
              (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥)
      path2 = path
              >=> (\i -> (∥-Bot ¬p i) ⊎ (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥))
              >=> (⊎-LiftBot (Σ[ i ∈ (Fin n) ] ∥ P (Fin.i i) ∥))

  boundedEquiv : {P : Pred Nat ℓ} -> (B : isBounded P) ->
                 Σ Nat P ≃ (Σ[ i ∈ Fin ⟨ B ⟩ ] (P (Fin.i i)))
  boundedEquiv {ℓ} {P} (b , f) = isoToEquiv i
    where
    open Iso
    i : Iso (Σ Nat P) (Σ[ i ∈ Fin b ] (P (Fin.i i)))
    i .fun (i , p) = (i , f p) , p
    i .inv ((i , lt), p) = i , p
    i .rightInv ((i , lt) , p) k = (i , isProp-≤ (f p) lt k) , p
    i .leftInv _ = refl

  boundedDecidable->isFinSet : {P : Pred Nat ℓ} -> isBounded P -> Decidable P ->
                               isFinSet (Σ[ n ∈ Nat ] ∥ P n ∥)
  boundedDecidable->isFinSet {P = P} (n , boundP) decP =
    subst isFinSet (sym (ua eq1)) isFin
    where
    boundP' : (Squash ∘ P) ⊆ (_< n)
    boundP' p = unsquash isProp-≤ (∥-map boundP p)


    eq1 : Σ Nat (Squash ∘ P) ≃ (Σ[ i ∈ Fin n ] ∥ P (Fin.i i) ∥)
    eq1 = boundedEquiv (n , boundP')

    isFin : isFinSet (Σ[ i ∈ Fin n ] ∥ P (Fin.i i) ∥)
    isFin = decidableSubset->isFinSet decP n

abstract
  boundedDecidableProp->isFinSet : {P : Pred Nat ℓ} -> isBounded P -> Decidable P ->
                                   ({n : Nat} -> isProp (P n)) ->
                                   isFinSet (Σ Nat P)
  boundedDecidableProp->isFinSet boundP decP isPropP =
    transport (\i -> isFinSet (Σ[ n ∈ Nat ] (∥-Prop (isPropP {n}) i)))
              (boundedDecidable->isFinSet boundP decP)
