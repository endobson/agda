{-# OPTIONS --cubical --safe --exact-split #-}

module graph.simple.inductive-walk where

open import base
open import equality-path
open import graph.simple

module _ {ℓV ℓE : Level} (G : Graph ℓV ℓE) where
  open Graph G

  data ForwardInductiveWalk : V -> V -> Type (ℓ-max ℓV ℓE) where
    walk-end  : (v : V) -> ForwardInductiveWalk v v
    walk-step : (v₁ v₂ v₃ : V) -> E v₁ v₂ -> ForwardInductiveWalk v₂ v₃ -> ForwardInductiveWalk v₁ v₃

module _ {ℓV ℓE : Level} {G : Graph ℓV ℓE} where
  open Graph G

  ForwardInductiveWalk-AvoidsVertex :
    {v₁ v₂ : V} -> ForwardInductiveWalk G v₁ v₂ -> V -> Type ℓV
  ForwardInductiveWalk-AvoidsVertex (walk-end v₁) v₂ = v₁ != v₂
  ForwardInductiveWalk-AvoidsVertex (walk-step v₁ _ _ _ w) v₂ =
    v₁ != v₂ × (ForwardInductiveWalk-AvoidsVertex w v₂)

  ForwardInductiveWalk-isPath : {v₁ v₂ : V} -> ForwardInductiveWalk G v₁ v₂ -> Type ℓV
  ForwardInductiveWalk-isPath (walk-end _) = Lift ℓV Top
  ForwardInductiveWalk-isPath (walk-step v _ _ _ w) =
    ForwardInductiveWalk-AvoidsVertex w v × ForwardInductiveWalk-isPath w
