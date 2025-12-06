{-# OPTIONS --cubical --safe --exact-split #-}

module graph.simple.walk-to-path where

open import base
open import equality-path
open import fin
open import graph.simple
open import graph.simple.walk-conversion
open import graph.simple.finite-walk
open import graph.simple.inductive-walk

module _ {ℓV ℓE : Level} {G : Graph ℓV ℓE}  where
  open Graph G

  opaque
    FiniteWalk->FinitePath :
      (w₁ : FiniteWalk G) ->
      Σ[ w₂ ∈ FiniteWalk G ] (FiniteWalk-isPath w₂ × FiniteWalk-SameEnds w₁ w₂)
    FiniteWalk->FinitePath w₀ = w₃ , p₃ , (sym start₃) , (sym end₃)
      where
      v₀ : V
      v₀ = FiniteWalk.vs w₀ zero-fin
      v₁ : V
      v₁ = FiniteWalk.vs w₀ max-fin

      w₁ : ForwardInductiveWalk G v₀ v₁
      w₁ = FiniteWalk->ForwardInductiveWalk w₀
      Σw₂ : Σ[ w ∈ ForwardInductiveWalk G v₀ v₁ ] (ForwardInductiveWalk-isPath w)
      Σw₂ = ForwardInductiveWalk->ForwardInductivePath w₁
      w₂ : ForwardInductiveWalk G v₀ v₁
      w₂ = fst Σw₂

      w₃ : FiniteWalk G
      w₃ = ForwardInductiveWalk->FiniteWalk w₂
      p₃ : FiniteWalk-isPath w₃
      p₃ = ForwardInductiveWalk->FiniteWalk-preserves-Path w₂ (snd Σw₂)
      start₃ : FiniteWalk-StartsWith w₃ v₀
      start₃ = ForwardInductiveWalk->FiniteWalk-StartsWith w₂
      end₃ : FiniteWalk-EndsWith w₃ v₁
      end₃ = ForwardInductiveWalk->FiniteWalk-EndsWith w₂
