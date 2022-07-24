{-# OPTIONS --cubical --safe --exact-split #-}

module equivalence where

open import base
open import cubical
open import equality-path
open import functions

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A A1 A2 : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> B a -> Type ℓ

-- fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
-- fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y


module _ {f : A1 -> A2} (eq-f : isEquiv f) where
  isEqFun : A1 -> A2
  isEqFun = f

  isEqInv : A2 -> A1
  isEqInv a = eq-f .equiv-proof a .fst .fst

  isEqSec : isSectionOf isEqFun isEqInv
  isEqSec a = eq-f .equiv-proof a .fst .snd

  isEqRet : isRetractionOf isEqFun isEqInv
  isEqRet a i = eq-f .equiv-proof (f a) .snd (a , refl) i .fst

  isEqComm : (a : A1) -> Square (isEqSec (f a)) refl (cong f (isEqRet a)) refl
  isEqComm a i = eq-f .equiv-proof (f a) .snd (a , refl) i .snd

module _ (e : A1 ≃ A2) where
  eqFun : A1 -> A2
  eqFun = fst e

  eqInv : A2 -> A1
  eqInv = isEqInv (snd e)

  eqSec : isSectionOf eqFun eqInv
  eqSec = isEqSec (snd e)

  eqRet : isRetractionOf eqFun eqInv
  eqRet = isEqRet (snd e)

  eqComm : (a : A1) -> Square (eqSec (eqFun a)) refl (cong eqFun (eqRet a)) refl
  eqComm = isEqComm (snd e)

  eqCtr : (a : A2) -> fiber eqFun a
  eqCtr a = e .snd .equiv-proof a .fst

  eqCtrPath : (a : A2) -> (f : fiber eqFun a) -> (eqCtr a) == f
  eqCtrPath a = e .snd .equiv-proof a .snd

idfun : (A : Type ℓ) → A → A
idfun _ x = x

idIsEquiv : (A : Type ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , \ z i -> z .snd (~ i) , \ j -> z .snd (~ i ∨ j))

idEquiv : (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

pathToEquiv : A1 == A2 -> A1 ≃ A2
pathToEquiv p = lineToEquiv (\i -> p i)



liftEquiv : {ℓA : Level} (ℓ : Level) (A : Type ℓA) -> Lift ℓ A ≃ A
liftEquiv ℓ A .fst = Lift.lower
liftEquiv ℓ A .snd .equiv-proof a = (lift a , refl) , contr a
  where
  contr : (a : A) -> (a2 : fiber Lift.lower a) -> (lift a , refl) == a2
  contr a (_ , p2) i = (lift (p2 (~ i)) , (\j -> p2 (~ i ∨ j)))

