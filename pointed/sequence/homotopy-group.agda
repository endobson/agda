{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.sequence.homotopy-group where

open import base
open import funext
open import equality-path
open import nat
open import hlevel.base
open import hlevel.pi
open import group
open import truncation
open import equivalence.base
open import truncation.set
open import functions
open import pointed.homotopy-group
open import pointed.base
open import pointed.truncation
open import pointed.loop-space
open import pointed.sequence.equivalence

import pointed.sequence as ps
import group-theory.exact-sequence as gs


pointedSequence->groupSequence : {ℓ : Level} -> ps.ℕ⁻-Sequence ℓ -> gs.ℕ⁻-Sequence ℓ
pointedSequence->groupSequence {ℓ} S = record
  { G = G
  ; fʰ = \n -> g n , gʰ n
  }
  where
  module S = ps.ℕ⁻-Sequence S
  G : ℕ -> Group ℓ
  G = loop-group ∘ S.Ty∙
  D : ℕ -> Type ℓ
  D = fst ∘ G

  g : (n : ℕ) -> D (suc n) -> D n
  g n = ∥₀-map (app∙ (Ωf (S.f∙ n)))

  gʰ : (n : ℕ) -> isGroupʰ (G (suc n)) (G n) (g n)
  gʰ n = record
    { preserves-ε = preserves-ε
    ; preserves-∙ = preserves-∙
    ; preserves-inverse = preserves-inverse
    }
    where
    module G₁ = Group (G (suc n))
    module G₂ = Group (G n)

    preserves-ε : g n G₁.ε == G₂.ε
    preserves-ε i = ∣ (->∙-path (Ωf (S.f∙ n)) i) ∣

    preserves-∙ : ∀ x y -> g n (x G₁.∙ y) == (g n x) G₂.∙ (g n y)
    preserves-∙ =
      ∥₀-elim2' (\x y -> isProp->isSet (G₂.isSet-Domain _ _)) inner
      where
      inner : ∀ (x y : ⟨ Ω (S.Ty∙ (suc n)) ⟩) ->
                Path (D n)
                (∣ (app∙ (Ωf (S.f∙ n))) (x >=> y) ∣)
                (∣ (app∙ (Ωf (S.f∙ n))) x >=> (app∙ (Ωf (S.f∙ n))) y ∣)
      inner x y i = ∣ Ωf->=> (S.f∙ n) x y i ∣

    preserves-inverse : ∀ x -> g n (G₁.inverse x) == G₂.inverse (g n x)
    preserves-inverse =
      ∥₀-elim' (\x -> isProp->isSet (G₂.isSet-Domain _ _))
        (\_ -> refl)

fiberSequence->exactSequence : {ℓ : Level} ->
  Σ (ps.ℕ⁻-Sequence ℓ) ps.isFiberSequence-ℕ⁻ ->
  Σ (gs.ℕ⁻-Sequence ℓ) gs.isExact-ℕ⁻-Sequence
fiberSequence->exactSequence {ℓ} (Sⁿ , Fⁿ) = (GS , record { isExact = isExact })
  where
  module Sⁿ = ps.ℕ⁻-Sequence Sⁿ
  module Fⁿ = ps.isFiberSequence-ℕ⁻ Fⁿ

  GS : gs.ℕ⁻-Sequence ℓ
  GS = pointedSequence->groupSequence Sⁿ
  module GS = gs.ℕ⁻-Sequence GS

  isExact : ∀ n -> gs.isExact-Pair (GS.fʰ (suc n)) (GS.fʰ n)
  isExact n = \b -> for b , back b
    where
    ΩS : ps.Short3Sequence ℓ ℓ ℓ
    ΩS = Ωf-Short3Sequence (Sⁿ.short3 n)
    ΩF : ps.isFiberSequence-Short3 ΩS
    ΩF = Ωf-Short3FiberSequence (Fⁿ.isFiberSeq-short3 n)
    module ΩS = ps.Short3Sequence ΩS
    module ΩF = ps.isFiberSequence-Short3 ΩF


    ★ : Squash₀ ΩS.C
    ★ = ∣ ΩS.★C ∣

    for : ∀ b -> ∥ fiber (∥₀-map ΩS.f) b ∥ -> (∥₀-map ΩS.g) b == ★
    for b = ∥-elim (\_ -> squash _ _) inner
      where
      inner : fiber (∥₀-map ΩS.f) b -> _
      inner (a , fa=b) = cong _ (sym fa=b) >=> step₂ a
        where
        step₂ : ∀ x -> (∥₀-map ΩS.g) ((∥₀-map ΩS.f) x) == ★
        step₂ = ∥₀-elim' (\_ -> isProp->isSet (squash _ _))
                         (\x i -> ∣ ΩF.isNull x i ∣)


    back : ∀ b -> (∥₀-map ΩS.g) b == ★ -> ∥ fiber (∥₀-map ΩS.f) b ∥
    back = ∥₀-elim' (\b -> isSetΠ (\_ -> isProp->isSet squash)) step₁
      where
      step₁ : (b : ΩS.B) ->
              ∣ ΩS.g b ∣ == ★ ->
              ∥ fiber (∥₀-map ΩS.f) ∣ b ∣ ∥
      step₁ b p = ∥-map step₂ q
        where
        q : Squash (ΩS.g b == ΩS.★C)
        q = eqInv (Squash-path-eq ΩS.C (ΩS.g b) ΩS.★C) p

        step₂ : (ΩS.g b == ΩS.★C) -> fiber (∥₀-map ΩS.f) ∣ b ∣
        step₂ p' = ∣ a ∣ , (\i -> ∣ fp i ∣)
          where
          fib : ⟨ fiber∙ ΩS.g∙ ⟩
          fib = b , p'
          a : ΩS.A
          a = isEqInv ΩF.isEquiv-total fib
          fp : ΩS.f a == b
          fp = cong fst (isEqSec ΩF.isEquiv-total fib)
