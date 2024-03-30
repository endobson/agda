{-# OPTIONS --cubical --safe --exact-split #-}

module category.limits where

open import base
open import category.base
open import category.constructions.cone
open import category.functor
open import category.object.terminal

module _ {ℓOJ ℓMJ ℓOC ℓMC : Level} {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
       (D : Diagram J C) where
  Limit : Type _
  Limit = Terminal (ConeC D)

hasLimitsOfShape : {ℓOJ ℓMJ ℓOC ℓMC : Level} (J : PreCategory ℓOJ ℓMJ) (C : PreCategory ℓOC ℓMC) -> Type _
hasLimitsOfShape J C = (D : Diagram J C) -> Limit D
