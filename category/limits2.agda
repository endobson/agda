{-# OPTIONS --cubical --safe --exact-split #-}

module category.limits2 where

open import base
open import category.base
open import category.constructions.cone
open import category.functor
open import category.object.terminal

-- TODO replace old limits file with this.

module _ {ℓOJ ℓMJ ℓOC ℓMC : Level} {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
       (D : Diagram J C) where
  Limit : Type _
  Limit = Terminal (ConeC D)
