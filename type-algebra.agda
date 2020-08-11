{-# OPTIONS --cubical --safe --exact-split #-}

module type-algebra where

open import base
open import commutative-monoid
open import equality
open import equivalence
open import isomorphism
open import monoid

open Iso

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

×-Bot : (A : Type ℓ) -> (Bot × A) == Lift ℓ Bot
×-Bot {ℓ} A = ua (isoToEquiv i)
  where
  i : Iso (Bot × A) (Lift ℓ Bot)
  i .fun (b , _)  = bot-elim b
  i .inv (lift b) = bot-elim b
  i .rightInv (lift b) = bot-elim b
  i .leftInv (b , _)   = bot-elim b

×-Top : (A : Type ℓ) -> (Top × A) == A
×-Top A = ua (isoToEquiv i)
  where
  i : Iso (Top × A) A
  i .fun (tt , a)  = a
  i .inv a         = (tt , a)
  i .rightInv _ = refl
  i .leftInv _ = refl

×-flip : {A B : Type ℓ} -> (A × B) == (B × A)
×-flip {A = A} {B} = ua (isoToEquiv i)
  where
  i : Iso (A × B) (B × A)
  i .fun (a , b) = (b , a)
  i .inv (b , a) = (a , b)
  i .rightInv _ = refl
  i .leftInv _ = refl

×-assoc : (A B C : Type ℓ) -> ((A × B) × C) == (A × (B × C))
×-assoc A B C = ua (isoToEquiv i)
  where
  i : Iso ((A × B) × C) (A × (B × C))
  i .fun ((a , b) , c) = (a , (b , c))
  i .inv (a , (b , c)) = ((a , b) , c)
  i .rightInv _ = refl
  i .leftInv _ = refl

instance
  ×-Monoid : Monoid (Type ℓ-zero)
  ×-Monoid = record
    { ε = Top
    ; _∙_ = _×_
    ; ∙-assoc = \{A B C} -> ×-assoc A B C
    ; ∙-left-ε = \{A} -> ×-Top A
    ; ∙-right-ε = \{A} -> ×-flip >=> ×-Top A
    }

  ×-CommMonoid : CommMonoid (Type ℓ-zero)
  ×-CommMonoid = record
    { ∙-commute = ×-flip
    }
