{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.sphere-hopf where

open import pointed.base
open import equivalence
open import hlevel
open import pointed.suspension
open import pointed.spheres
open import pointed.hspace
open import cubical
open import funext
open import equality-path
open import equality.square
open import base
open import connected
open import truncation
open import truncation.generic
open import truncation.generic.path
open import univalence
open import pushout
open import pushout.spheres
open import pushout.flattening


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
  
  
  isConnected-S¹' : isConnectedₙ 2 S¹
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

  isConnected-S¹ : isConnectedₙ 2 (Sⁿ 1)
  isConnected-S¹ = transport (\i -> isConnectedₙ 2 (ua S¹≃Sⁿ i)) isConnected-S¹'



  HSpaceStr-S¹ : HSpaceStr (Sⁿ∙ 1)
  HSpaceStr-S¹ = 
    transport 
      (\i -> HSpaceStr (ua S¹≃Sⁿ i , ua-glue S¹≃Sⁿ i (\{ (i = i0) -> base }) (inS north))) 
      HSpaceStr-S¹'
  
  ConnectedHSpace-S¹ : ConnectedHSpace ℓ-zero
  ConnectedHSpace-S¹ = ((Sⁿ∙ 1) , HSpaceStr-S¹) , isConnected-S¹


  hopf₁ : (Sⁿ 2) -> Type₀
  hopf₁ = hopf-construction₁ ConnectedHSpace-S¹

  hopf₁-∙ : hopf₁ north == Sⁿ 1
  hopf₁-∙ = refl

  hopf₂ : Σ (Sⁿ 2) hopf₁ == (Sⁿ 3)
  hopf₂ = hopf-construction₂ ConnectedHSpace-S¹ >=> ua (Sphere-Join-eq 1 1)

  hopf-map : (Sⁿ 3) -> (Sⁿ 2)
  hopf-map x = fst (transport (sym hopf₂) x)





