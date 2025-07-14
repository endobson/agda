{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.sphere-hopf where

open import base
open import connected
open import cubical
open import equality-path
open import equality.square
open import equivalence
open import funext
open import functions
open import hlevel
open import pointed.base
open import pointed.hspace
open import pointed.homotopy-group
open import pointed.sequence
open import pointed.loop-space
open import pointed.sequence.loops
open import pointed.sequence.homotopy-group
open import pointed.spheres
open import pointed.suspension
open import pushout
open import pushout.flattening
open import pushout.spheres
open import truncation
open import truncation.generic
open import truncation.generic.path
open import univalence

import group-theory.exact-sequence as gs


private
  HSpaceStr-S¹' : HSpaceStr S¹∙
  HSpaceStr-S¹' =
    hspace-str μ μ-left μ-right μ-same
    where

    loop-x : ∀ (x : S¹) -> x == x
    loop-x base       = loop
    loop-x (loop i) j =
      hcomp (\k -> \{ (i = i0) -> loop (j ∨ (~ k))
                    ; (i = i1) -> loop (j ∧ k)
                    ; (j = i0) -> loop (i ∨ (~ k))
                    ; (j = i1) -> loop (i ∧ k)
                    })
        base


    μ : S¹ -> S¹ -> S¹
    μ base     x = x
    μ (loop i) x = loop-x x i

    μ-left : ∀ x -> μ base x == x
    μ-left _ = refl
    μ-right : ∀ x -> μ x base == x
    μ-right base = refl
    μ-right (loop i) = refl

    μ-same : μ-left base == μ-right base
    μ-same = refl


  isConnected-S¹' : isConnected S¹
  isConnected-S¹' = squashₙ 2 base , ∥ₙ-elim h f
    where
    h : ∀ y -> isOfHLevel 2 (squashₙ 2 base == y)
    h y = isOfHLevelPath 2 (isOfHLevel-Squashₙ 2) _ _
    f : ∀ x -> squashₙ 2 base == squashₙ 2 x
    f x =
      eqFun (squashed-path-eq 1 base x)
        (unsquash (isOfHLevel-Squashₙ 1) (∥-map (squashₙ 1) (mere-path x)))
      where

      mere-path : ∀ x -> ∥ Path S¹ base x ∥
      mere-path base = ∣ refl ∣
      mere-path (loop i) = transP-left pp p2 i
        where
        pp : PathP (\i -> ∥ base == loop i ∥) (∣ refl ∣) (∣ loop ∣)
        pp i = ∣ (\j -> loop (i ∧ j)) ∣

        p2 : Path (∥ base == base ∥) (∣ loop ∣) (∣ refl ∣)
        p2 = squash _ _

  isConnected-S¹ : isConnected (Sⁿ 1)
  isConnected-S¹ = transport (\i -> isConnected (ua S¹≃Sⁿ i)) isConnected-S¹'



  HSpaceStr-S¹ : HSpaceStr (Sⁿ∙ 1)
  HSpaceStr-S¹ =
    transport
      (\i -> HSpaceStr (ua S¹≃Sⁿ i , ua-glue S¹≃Sⁿ i (\{ (i = i0) -> base }) (inS north)))
      HSpaceStr-S¹'

  ConnectedHSpace-S¹ : ConnectedHSpace ℓ-zero
  ConnectedHSpace-S¹ = ((Sⁿ∙ 1) , HSpaceStr-S¹) , isConnected-S¹


  hopf₁ : (Sⁿ 2) -> Type₀
  hopf₁ = hopf-fibration ConnectedHSpace-S¹

  hopf₁-∙ : hopf₁ north == Sⁿ 1
  hopf₁-∙ = refl

  total-eq∙ : Σ∙ (Sⁿ∙ 2) hopf₁ north ≃∙ (Sⁿ∙ 3)
  total-eq∙ =
    hopf-join-eq∙ ConnectedHSpace-S¹ >≃∙> Sphere-Join-eq∙ 1 1

  hopf₂ : Σ (Sⁿ 2) hopf₁ == (Sⁿ 3)
  hopf₂ = cong fst (Type∙-path total-eq∙)

  hopf-map : (Sⁿ 3) -> (Sⁿ 2)
  hopf-map x = fst (transport (sym hopf₂) x)

  hopf-fiber-sequence : Σ (ℕ⁻-Sequence ℓ-zero) isFiberSequence-ℕ⁻
  hopf-fiber-sequence = puppe-sequence (Sⁿ∙ 2) hopf₁ north

  hopf-group-sequence : Σ (gs.ℕ⁻-Sequence ℓ-zero) gs.isExact-ℕ⁻-Sequence
  hopf-group-sequence = fiberSequence->exactSequence hopf-fiber-sequence

  module S = gs.ℕ⁻-Sequence ⟨ hopf-group-sequence ⟩


  check₀ : S.G 0 == loop-group (Sⁿ∙ 2)
  check₀ = refl

  check₁ : S.G 1 == loop-group (Sⁿ∙ 3)
  check₁ = cong loop-group (Type∙-path total-eq∙)

  check₂ : S.G 2 == loop-group (Sⁿ∙ 1)
  check₂ = refl

  check₃ : S.G 3 == loop-group (Ω (Sⁿ∙ 2))
  check₃ = refl

  check₄ : S.G 4 == loop-group (Ω (Sⁿ∙ 3))
  check₄ = cong (loop-group ∘ Ω) (Type∙-path total-eq∙)


  check-5 : S.G 5 == πₙ (2 , tt) (Sⁿ∙ 1)
  check-5 = refl

  check-6 : S.G 6 == πₙ (3 , tt) (Sⁿ∙ 2)
  check-6 = refl

  check-7 : S.G 7 == πₙ (3 , tt) (Sⁿ∙ 3)
  check-7 = cong (loop-group ∘ Ωⁿ 2) (Type∙-path total-eq∙)

  check-8 : S.G 8 == πₙ (3 , tt) (Sⁿ∙ 1)
  check-8 = refl
