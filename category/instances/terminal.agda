{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import hlevel

module category.instances.terminal where

private
  TermSorts : CategorySorts ℓ-zero ℓ-zero
  TermSorts .CategorySorts.Obj = Top
  TermSorts .CategorySorts.Mor _ _ = Top

  TermOps : CategoryOps TermSorts
  TermOps .CategoryOps.id = tt
  TermOps .CategoryOps._⋆_ _ _ = tt

  TermLaws : CategoryLaws TermOps
  TermLaws .CategoryLaws.⋆-left-id _ = refl
  TermLaws .CategoryLaws.⋆-right-id _ = refl
  TermLaws .CategoryLaws.⋆-assoc _ _ _ = refl
  TermLaws .CategoryLaws.isSet-Mor = isProp->isSet isPropTop

TermC : PreCategory ℓ-zero ℓ-zero
TermC = Laws->Category TermLaws
