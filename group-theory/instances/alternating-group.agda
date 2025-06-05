{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.instances.alternating-group where

open import base
open import equality-path
open import equivalence
open import fin
open import hlevel.base
open import hlevel.equivalence
open import truncation
open import truncation.generic
open import truncation.generic.path
open import truncation.generic.truncated
open import pointed.base
open import pointed.loop-space
open import connected
open import group
open import group-theory.instances.isomorphism
open import new-permutation
open import univalence
open import sigma.base

{-
module _ (n : Nat) where
  BSym : Type₁
  BSym = Σ[ T ∈ Type₀ ] ∥ T ≃ (Fin n) ∥

  BSym∙ : Type∙ ℓ-one
  BSym∙ = BSym , (Fin n , ∣ idEquiv _ ∣ )

  isConnected-BSym : isConnectedₙ 2 BSym
  isConnected-BSym =
    ∣ (snd BSym∙) ∣ , isProp-Squash₂-BSym _
    where
    opaque
      Squash₁-path : ∀ (x y : BSym) -> Squashₙ 1 (x == y)
      Squash₁-path (X , ex) (Y , ey) =
        unsquash (isOfHLevel-Squashₙ 1)
          (∥-map2 (\ex ey -> ∣ ΣProp-path squash (ua ex >=> sym (ua ey)) ∣) ex ey)

      squash₂-path : ∀ (x y : BSym) -> squashₙ 2 x == squashₙ 2 y
      squash₂-path x y = eqFun (squashed-path-eq 1 x y) (Squash₁-path x y)

      isProp-Squash₂-BSym : isProp (Squashₙ 2 BSym)
      isProp-Squash₂-BSym =
        ∥ₙ-elim2 (\x y -> isOfHLevelPath 1 (isOfHLevel-Squashₙ 2 x y)) squash₂-path

  Sym∙ : Type ℓ-one
  Sym∙ = Ω BSym∙
-}

SymG : (n : Nat) -> Group ℓ-zero
SymG n = Perm n , useⁱ
