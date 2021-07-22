{-# OPTIONS --cubical --safe --exact-split #-}

module subset where

open import base
open import finset
open import functions
open import hlevel
open import relation
open import truncation

-- A subspace of the space D
Subspace : {ℓD : Level} -> (D : Type ℓD) -> (ℓP : Level) -> Type (ℓ-max ℓD (ℓ-suc ℓP))
Subspace D ℓP = (D -> hProp ℓP)

module _ {ℓD ℓS : Level} {D : Type ℓD} (S : Subspace D ℓS) where
  ∈-Subspace : Type (ℓ-max ℓD ℓS)
  ∈-Subspace = Σ[ d ∈ D ] ⟨ S d ⟩

  isFiniteSubspace : Type _
  isFiniteSubspace = isFinSet ∈-Subspace


-- Family of Ds indexed by I
Family : {ℓD ℓI : Level} -> Type ℓD -> Type ℓI -> Type (ℓ-max ℓD ℓI)
Family D I = I -> D

Family->Subspace : {ℓD ℓI : Level} -> {D : Type ℓD} -> {I : Type ℓI} ->
                   Family D I -> Subspace D (ℓ-max ℓD ℓI)
Family->Subspace {I = I} f d = (∃[ i ∈ I ] (f i == d)) , squash


-- A FinSubset is a finite amount of Ds
FinSubset : {ℓD : Level} (D : Type ℓD) (ℓI : Level) -> Type (ℓ-max ℓD (ℓ-suc ℓI))
FinSubset D ℓI = Σ[ I ∈ (FinSet ℓI) ] Σ[ f ∈ (⟨ I ⟩ -> D) ] (Injective f)
