{-# OPTIONS --cubical --safe --exact-split #-}

module graph.simple.finite-walk where

open import base
open import fin
open import functions
open import graph.simple
open import nat
open import relation

module _ {ℓV ℓE : Level} (G : Graph ℓV ℓE) where
  open Graph G

  record FiniteWalk : Type (ℓ-max ℓV ℓE) where
    constructor finite-walk
    field
      N : ℕ
      vs : Fin (suc N) -> V
      es : ∀ i -> E (vs (inc-fin i)) (vs (suc-fin i))

    length : ℕ
    length = suc N


module _ {ℓV ℓE : Level} {G : Graph ℓV ℓE} where
  open Graph G

  FiniteWalk-isPath : Pred (FiniteWalk G) ℓV
  FiniteWalk-isPath w = isEmbedding (FiniteWalk.vs w)
  FiniteWalk-StartsWith : REL (FiniteWalk G) V ℓV
  FiniteWalk-StartsWith w v = FiniteWalk.vs w zero-fin == v
  FiniteWalk-EndsWith : REL (FiniteWalk G) V ℓV
  FiniteWalk-EndsWith w v = FiniteWalk.vs w max-fin == v

  FiniteWalk-SameEnds : Rel (FiniteWalk G) ℓV
  FiniteWalk-SameEnds w₁ w₂ =
    (FiniteWalk.vs w₁ zero-fin == FiniteWalk.vs w₂ zero-fin) ×
    (FiniteWalk.vs w₁ max-fin  == FiniteWalk.vs w₂ max-fin)

module _ {ℓV ℓE : Level} (G : Graph ℓV ℓE) where
  GPath : Type (ℓ-max ℓV ℓE)
  GPath = Σ (FiniteWalk G) FiniteWalk-isPath

module _ {ℓV ℓE : Level}  where
  isTree : Pred (Graph ℓV ℓE) (ℓ-max ℓV ℓE)
  isTree G = ∀ v₁ v₂ -> Σ[ w ∈ FiniteWalk G ] (
    FiniteWalk-isPath w ×
    FiniteWalk-StartsWith w v₁ ×
    FiniteWalk-EndsWith w v₂)
