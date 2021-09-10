{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid.subtype where

open import base
open import commutative-monoid
open import equality
open import hlevel
open import monoid
open import monoid.subtype
open import relation
open import sigma

module _ {ℓ₁ ℓ₂ : Level} {D : Type ℓ₁} {P : Pred D ℓ₂}
         (isProp-P : isPropValuedPred P) (M : CommMonoid D) where
  private
    module M = CommMonoid M

  SubCommMonoidStr : P (M.ε) -> ClosedUnder M._∙_ P -> CommMonoid (Σ D P)
  SubCommMonoidStr Pε closed = record
    { monoid = SubMonoidStr isProp-P M.monoid Pε closed
    ; ∙-commute = ΣProp-pathᵉ (isProp-P _) M.∙-commute
    ; isSet-Domain = isSetΣ M.isSet-Domain (\d -> isProp->isSet (isProp-P d))
    }
