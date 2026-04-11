{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.loop-space where

open import base
open import equality-path
open import equivalence
open import nat
open import nat.iteration
open import pointed.base

Ω : {ℓ : Level} -> Type∙ ℓ -> Type∙ ℓ
Ω (A , ★A) = (★A == ★A) , refl

Ωⁿ : {ℓ : Level} -> Nat -> Type∙ ℓ -> Type∙ ℓ
Ωⁿ n = iter n Ω

Ω² : {ℓ : Level} -> Type∙ ℓ -> Type∙ ℓ
Ω² = Ωⁿ 2

Ωf : {ℓA ℓB : Level} {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} ->
     (A∙ ->∙ B∙) -> (Ω A∙ ->∙ Ω B∙)
Ωf {A∙ = (A , ★A)} {B∙ = (B , ★B)} (->∙-cons f fp) = (->∙-cons f' fp')
  where
  f' : (★A == ★A) -> (★B == ★B)
  f' ap = sym fp ∙∙ (cong f ap) ∙∙ fp

  fp' : f' refl == refl
  fp' = compPath-sym (sym fp)

Ω-Ωⁿ-path : {ℓ : Level} {A∙ : Type∙ ℓ} (n : Nat) ->
            Ω (Ωⁿ n A∙) == (Ωⁿ n (Ω A∙))
Ω-Ωⁿ-path zero    = refl
Ω-Ωⁿ-path (suc n) = cong Ω (Ω-Ωⁿ-path n)
