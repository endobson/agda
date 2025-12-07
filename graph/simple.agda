{-# OPTIONS --cubical --safe --exact-split #-}

module graph.simple where

open import base
open import decision
open import discrete
open import finset
open import functions
open import hlevel.base

record Graph (ℓV ℓE : Level) : Type (ℓ-suc (ℓ-max ℓV ℓE)) where
  field
    V : Type ℓV
    E : Rel V ℓE

    isFinSet-V : isFinSet V

    isProp-E : ∀ v₁ v₂ -> isProp (E v₁ v₂)
    dec-E : ∀ v₁ v₂ -> Dec (E v₁ v₂)
    refl-E : ∀ v -> E v v
    sym-E : ∀ v₁ v₂ -> E v₁ v₂ -> E v₂ v₁

  opaque
    isSet-V : isSet V
    isSet-V = isFinSet->isSet isFinSet-V

    instance
      Discrete'-V : Discrete' V
      Discrete'-V = record { f = isFinSet->Discrete isFinSet-V }

module _ {ℓV ℓE : Level} (G₁ G₂ : Graph ℓV ℓE) where
  private
    module G₁ = Graph G₁
    module G₂ = Graph G₂

  record GraphMor : Type (ℓ-max ℓV ℓE) where
    constructor graph-mor
    field
      vf : G₁.V -> G₂.V
      ef : ∀ v₁ v₂ -> G₁.E v₁ v₂ -> G₂.E (vf v₁) (vf v₂)

isGraphEmbedding : {ℓV ℓE : Level} {G₁ G₂ : Graph ℓV ℓE} -> GraphMor G₁ G₂ -> Type ℓV
isGraphEmbedding (graph-mor vf ef) = isEmbedding vf

module _ {ℓV ℓE : Level} (G₁ : Graph ℓV ℓE) where
  Subgraph : Type (ℓ-suc (ℓ-max ℓV ℓE))
  Subgraph = Σ[ G₂ ∈ Graph ℓV ℓE ] Σ (GraphMor G₂ G₁) isGraphEmbedding
