{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.sequence.fibered where

open import base
open import cubical
open import equality-path
open import equivalence
open import equivalence.base
open import functions
open import hlevel.base
open import isomorphism
open import nat
open import pointed.base
open import pointed.sequence
open import type-algebra
open import univalence


module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  open Short3Sequence S

  record isFiberSequence-Short3₂ : Type (ℓ-max* 3 ℓA ℓB ℓC) where
    field
      isNull : ∀ a -> app∙ g∙ (app∙ f∙ a) == ★C
      isNull-Square :
        Square (isNull ★A) (->∙-path g∙) (cong (app∙ g∙) (->∙-path f∙)) refl

    total : A -> fiber (app∙ g∙) ★C
    total a = app∙ f∙ a , (isNull a)

    total∙ : A∙ ->∙ fiber∙ g∙
    total∙ = ->∙-cons total (\i -> fp i , isNull-Square i)


    field
      isEquiv-total : isEquiv total




-- module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
--   open Short3Sequence S
--
--   record isFiberSequence-Short3'2 : Type (ℓ-max* 3 ℓA ℓB ℓC) where
--     field
--       isNull : f∙ >∙> g∙ == const->∙
--
--     total : A -> ⟨ fiber∙ g∙ ⟩
--     total a = app∙ f∙ a , (\i -> app∙ (isNull i) a)
--
--     total∙ : A∙ ->∙ fiber∙ g∙
--     total∙ = ->∙-cons total ?
--
--     field
--       isEquiv-total : isEquiv total
