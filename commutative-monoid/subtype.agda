{-# OPTIONS --cubical --safe --exact-split #-}

module commutative-monoid.subtype where

open import base
open import commutative-monoid
open import hlevel
open import monoid.subtype
open import relation
open import sigma.base

module _ {ℓ₁ ℓ₂ : Level} {D : Type ℓ₁} {P : Pred D ℓ₂}
         (isProp-P : isPropValuedPred P) (M : CommMonoid D) where
  private
    module M = CommMonoid M

  SubCommMonoidStr : P (M.ε) -> ClosedUnder M._∙_ P -> CommMonoid (Σ D P)
  SubCommMonoidStr Pε closed = record
    { monoid = SubMonoidStr isProp-P M.monoid Pε closed
    ; ∙-commute = ΣProp-path (isProp-P _) M.∙-commute
    }

module _ {ℓ₁ ℓ₂ : Level} {D : Type ℓ₁} {P : Pred D ℓ₂}
         {isProp-P : isPropValuedPred P} {M : CommMonoid D}
         {Pε : P (CommMonoid.ε M)} {P∙ : ClosedUnder (CommMonoid._∙_ M) P}
         where
  CommMonoidʰ-fst : CommMonoidʰᵉ (SubCommMonoidStr isProp-P M Pε P∙) M fst
  CommMonoidʰ-fst .CommMonoidʰ.preserves-ε = refl
  CommMonoidʰ-fst .CommMonoidʰ.preserves-∙ x y = refl
