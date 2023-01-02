{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid.hprop where

open import base
open import equality
open import hlevel
open import commutative-monoid
open import monoid
open import sigma.base
open import type-algebra

module _ where
  open Monoid
  ∧MonoidStr-hProp : (ℓ : Level) -> Monoid (hProp ℓ)
  ∧MonoidStr-hProp ℓ .ε = Lift ℓ Top , isProp-Lift isPropTop
  ∧MonoidStr-hProp ℓ ._∙_ (T , pT) (S , pS) =
    (T × S) , isProp× pT pS
  ∧MonoidStr-hProp ℓ .∙-assoc {(T , pT)} {(S , pS)} {(R , pR)} =
    ΣProp-path isProp-isProp (×-assoc T S R)
  ∧MonoidStr-hProp ℓ .∙-left-ε {(T , PT)} =
    ΣProp-path isProp-isProp (×-LiftTop T)
  ∧MonoidStr-hProp ℓ .∙-right-ε {(T , PT)} =
    ΣProp-path isProp-isProp (×-flip >=> ×-LiftTop T)


∧CommMonoidStr-hProp : (ℓ : Level) -> CommMonoid (hProp ℓ)
∧CommMonoidStr-hProp ℓ = record
  { monoid = ∧MonoidStr-hProp ℓ
  ; ∙-commute = ΣProp-path isProp-isProp ×-flip
  ; isSet-Domain = isSet-hProp
  }
