{-# OPTIONS --cubical --safe --exact-split #-}

module category.morphism where

open import base
open import category.base
open import equality
open import relation

module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  open CategoryHelpers C

  isMono : {a b : Obj C} -> Pred (C [ a , b ]) _
  isMono {a} {b} f =
    ∀ {c : Obj C} {g₁ g₂ : C [ c , a ]} ->
    g₁ ⋆ f == g₂ ⋆ f -> g₁ == g₂

  isEpi : {a b : Obj C} -> Pred (C [ a , b ]) _
  isEpi {a} {b} f =
    ∀ {c : Obj C} {g₁ g₂ : C [ b , c ]} ->
    f ⋆ g₁ == f ⋆ g₂ -> g₁ == g₂
