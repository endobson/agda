{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.subtype where

open import base
open import equality
open import monoid
open import relation
open import sigma.base

module _ {ℓ₁ ℓ₂ : Level} {D : Type ℓ₁} {P : Pred D ℓ₂}
         (isProp-P : isPropValuedPred P) (M : Monoid D) where
  private
    module M = Monoid M

  SubMonoidStr : P (M.ε) -> ClosedUnder M._∙_ P -> Monoid (Σ D P)
  SubMonoidStr Pε closed = record
    { ε = M.ε , Pε
    ; _∙_ = \(x , px) (y , py) -> x M.∙ y , closed px py
    ; ∙-assoc = ΣProp-path (isProp-P _) M.∙-assoc
    ; ∙-left-ε = ΣProp-path (isProp-P _) M.∙-left-ε
    ; ∙-right-ε = ΣProp-path (isProp-P _) M.∙-right-ε
    }
