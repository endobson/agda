{-# OPTIONS --cubical --safe --exact-split #-}

module subset where

open import base
open import cubical
open import equality
open import fin
open import finset
open import functions
open import hlevel
open import isomorphism
open import relation
open import truncation

-- A subtype of the type D
Subtype : {ℓD : Level} -> (D : Type ℓD) -> (ℓP : Level) -> Type (ℓ-max ℓD (ℓ-suc ℓP))
Subtype D ℓP = (D -> hProp ℓP)

module _ {ℓD ℓS : Level} {D : Type ℓD} (S : Subtype D ℓS) where
  ∈-Subtype : Type (ℓ-max ℓD ℓS)
  ∈-Subtype = Σ[ d ∈ D ] ⟨ S d ⟩

  ∉-Subtype : Type (ℓ-max ℓD ℓS)
  ∉-Subtype = Σ[ d ∈ D ] (¬ ⟨ S d ⟩)

  isFiniteSubtype : Type _
  isFiniteSubtype = isFinSet ∈-Subtype

  isFullSubtype : Type _
  isFullSubtype = ∀ (d : D) -> ⟨ S d ⟩


-- Family of Ds indexed by I
Family : {ℓD ℓI : Level} -> Type ℓD -> Type ℓI -> Type (ℓ-max ℓD ℓI)
Family D I = I -> D

Family->Subtype : {ℓD ℓI : Level} -> {D : Type ℓD} -> {I : Type ℓI} ->
                   Family D I -> Subtype D (ℓ-max ℓD ℓI)
Family->Subtype {I = I} f d = (∃[ i ∈ I ] (f i == d)) , squash


-- A FinSubset is a finite amount of Ds
FinSubset : {ℓD : Level} (D : Type ℓD) (ℓI : Level) -> Type (ℓ-max ℓD (ℓ-suc ℓI))
FinSubset D ℓI = Σ[ I ∈ (FinSet ℓI) ] Σ[ f ∈ (⟨ I ⟩ -> D) ] (Injective f)

-- A Detachable subtype is a subtype for which membership is decidable
Detachable : {ℓD ℓ : Level} {D : Type ℓD} -> Subtype D ℓ -> Type (ℓ-max ℓD ℓ)
Detachable P = Decidable (fst ∘ P)


-- Partitions

FinitePartition' : {ℓD : Level} -> (n : Nat) -> (D : Type ℓD) -> (ℓP : Level) -> Type _
FinitePartition' n D ℓP =
  Σ[ f ∈ (Fin n -> Subtype D ℓP) ] ((d : D) -> isContr (Σ[ i ∈ Fin n ] ⟨ f i d ⟩))

FinitePartition : {ℓD : Level} -> (D : Type ℓD) -> (ℓP : Level) -> Type _
FinitePartition D ℓP = Σ[ n ∈ Nat ] (FinitePartition' n D ℓP)

BinaryPartition : {ℓD : Level} -> (D : Type ℓD) -> (ℓP : Level) -> Type _
BinaryPartition = FinitePartition' 2


-- Complement of subtypes
Subtype-Comp : {ℓD ℓP : Level} -> {D : Type ℓD} -> Subtype D ℓP -> Subtype D ℓP
Subtype-Comp S d = (¬ ⟨ S d ⟩) , isProp¬ _

Detachable-Comp : {ℓD ℓP : Level} -> {D : Type ℓD} -> (S : Subtype D ℓP) ->
                  (Detachable S) -> (Detachable (Subtype-Comp S))
Detachable-Comp S decide-S d = comp-dec (decide-S d)

-- Equivalence
Detachable-eq : {ℓD ℓP : Level} -> {D : Type ℓD} -> (S : Subtype D ℓP) -> (Detachable S) ->
                D ≃ ((∈-Subtype S) ⊎ (∉-Subtype S))
Detachable-eq {D = D} S decide = isoToEquiv i
  where
  split : {d : D} -> Dec ⟨ S d ⟩ -> ((∈-Subtype S) ⊎ (∉-Subtype S))
  split {d} (yes s) = inj-l (d , s)
  split {d} (no ¬s) = inj-r (d , ¬s)

  open Iso
  i : Iso D ((∈-Subtype S) ⊎ (∉-Subtype S))
  i .fun d = split (decide d)
  i .inv (inj-l (d , s)) = d
  i .inv (inj-r (d , s)) = d

  i .leftInv d = path (decide d)
    where
    path : (dec : (Dec ⟨ S d ⟩)) -> i .inv (split dec) == d
    path (yes _) = refl
    path (no _) = refl

  i .rightInv (inj-l (d , s)) = cong split path
    where
    path : decide d == yes s
    path = isPropDec (snd (S d)) _ _
  i .rightInv (inj-r (d , ¬s)) = cong split path
    where
    path : decide d == no ¬s
    path = isPropDec (snd (S d)) _ _
