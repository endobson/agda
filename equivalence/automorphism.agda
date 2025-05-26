{-# OPTIONS --cubical --safe --exact-split #-}

module equivalence.automorphism where

open import base
open import equivalence
open import funext
open import group
open import hlevel
open import monoid
open import sigma.base

Monoid-Auto : {ℓ : Level} {A : Type ℓ} -> isSet A -> Monoid (Auto A)
Monoid-Auto {A = A} isSet-A = record
  { ε = idEquiv A
  ; _∙_ = ∘-equiv
  ; ∙-assoc = ΣProp-path isProp-isEquiv refl
  ; ∙-left-ε = ΣProp-path isProp-isEquiv refl
  ; ∙-right-ε = ΣProp-path isProp-isEquiv refl
  ; isSet-Domain = isSet-≃ isSet-A isSet-A
  }

GroupStr-Auto : {ℓ : Level} {A : Type ℓ} -> isSet A -> GroupStr (Auto A)
GroupStr-Auto {A = A} isSet-A = record
  { monoid = Monoid-Auto isSet-A
  ; inverse = equiv⁻¹
  ; ∙-left-inverse = \{e} -> ΣProp-path isProp-isEquiv (funExt (\a -> (eqRet e a)))
  ; ∙-right-inverse = \{e} -> ΣProp-path isProp-isEquiv (funExt (\a -> (eqSec e a)))
  }
