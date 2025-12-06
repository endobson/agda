{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.equivalence where

open import base
open import equivalence
open import funext
open import hlevel.base
open import hlevel.pi
open import hlevel.retract
open import hlevel.sigma
open import isomorphism
open import sigma.base

private
  variable
    ℓ : Level
    A₁ A₂ : Type ℓ

opaque
  -- h-level for equivalences and paths

  isContr->Iso : (isContr A₁) -> (isContr A₂) -> Iso A₁ A₂
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.fun _ = a2
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.inv _ = a1
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.rightInv = f2
  isContr->Iso (a1 , f1) (a2 , f2) .Iso.leftInv = f1

  isContr->Equiv : (isContr A₁) -> (isContr A₂) -> A₁ ≃ A₂
  isContr->Equiv c1 c2 = isoToEquiv (isContr->Iso c1 c2)

  isContr-≃ : (isContr A₁) -> (isContr A₂) -> (isContr (A₁ ≃ A₂))
  isContr-≃ {A₁ = A₁} {A₂ = A₂} c1@(a1 , f1) c2@(a2 , f2) = e1 , f
    where
    e1 : A₁ ≃ A₂
    e1 = isContr->Equiv c1 c2

    f : (e2 : A₁ ≃ A₂) -> e1 == e2
    f e2 = ΣProp-path isProp-isEquiv (funExt (\a1' -> (f2 (e2 .fst a1'))))


  isOfHLevel-≃ : (n : Nat) -> (isOfHLevel n A₁) -> (isOfHLevel n A₂) -> (isOfHLevel n (A₁ ≃ A₂))
  isOfHLevel-≃ 0 = isContr-≃
  isOfHLevel-≃ (suc n) h1 h2 =
    isOfHLevelΣ (suc n) (isOfHLevelΠ (suc n) (\ _ -> h2))
                (\_ -> isProp->isOfHLevelSuc n isProp-isEquiv)

  isProp-≃ : (isProp A₁) -> (isProp A₂) -> (isProp (A₁ ≃ A₂))
  isProp-≃ = isOfHLevel-≃ 1

  isSet-≃ : (isSet A₁) -> (isSet A₂) -> (isSet (A₁ ≃ A₂))
  isSet-≃ = isOfHLevel-≃ 2

  isProp-≃-right : (isProp A₂) -> (isProp (A₁ ≃ A₂))
  isProp-≃-right pA2 (f1 , e1) (f2 , e2) = ΣProp-path (isProp-isEquiv) f-path
    where
    f-path : f1 == f2
    f-path = funExt (\x -> pA2 _ _)

  isProp-≃-left : (isProp A₁) -> (isProp (A₁ ≃ A₂))
  isProp-≃-left pA1 e1 e2 = isProp-≃-right (isProp-Retract (eqInv e1) (eqFun e1) (eqSec e1) pA1) e1 e2

opaque
  -- Equivalent types have the same hlevel
  ≃-isOfHLevel : A₁ ≃ A₂ -> (n : Nat) -> isOfHLevel n A₁ -> isOfHLevel n A₂
  ≃-isOfHLevel eq n = isOfHLevel-Retract n (eqInv eq) (eqFun eq) (eqSec eq)

  ≃-isContr : A₁ ≃ A₂ -> isContr A₁ -> isContr A₂
  ≃-isContr eq = ≃-isOfHLevel eq 0

  ≃-isProp : A₁ ≃ A₂ -> isProp A₁ -> isProp A₂
  ≃-isProp eq = ≃-isOfHLevel eq 1

  ≃-isSet : A₁ ≃ A₂ -> isSet A₁ -> isSet A₂
  ≃-isSet eq = ≃-isOfHLevel eq 2
