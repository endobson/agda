{-# OPTIONS --cubical --safe --exact-split #-}

module equivalence.base where

open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv
        ; equiv-proof
        ; _≃_
        )

open import Agda.Builtin.Cubical.Glue
  using (module Helpers)

open Helpers public
  using ( fiber
        )

open import base
open import cubical

private
  variable
    ℓ : Level
    A B A1 A2 : Type ℓ

-- fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
-- fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

-- record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
--  no-eta-equality
--  field
--    equiv-proof : (y : B) → isContr (fiber f y)

idfun : (A : Type ℓ) → A → A
idfun _ x = x

idIsEquiv : (A : Type ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , \ z i -> z .snd (~ i) , \ j -> z .snd (~ i ∨ j))

idEquiv : (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

-- Private definitions to avoid circularity issues.
private
  isSectionOf : (A -> B) -> (B -> A) -> Type _
  isSectionOf f g = ∀ b -> f (g b) == b

  isRetractionOf : (A -> B) -> (B -> A) -> Type _
  isRetractionOf f g = ∀ a -> g (f a) == a


module _ {f : A1 -> A2} (eq-f : isEquiv f) where
  isEqFun : A1 -> A2
  isEqFun = f

  isEqInv : A2 -> A1
  isEqInv a = eq-f .equiv-proof a .fst .fst

  isEqSec : isSectionOf isEqFun isEqInv
  isEqSec a = eq-f .equiv-proof a .fst .snd

  isEqRet : isRetractionOf isEqFun isEqInv
  isEqRet a i = eq-f .equiv-proof (f a) .snd (a , refl) i .fst

module _ (e : A1 ≃ A2) where
  eqFun : A1 -> A2
  eqFun = fst e

  eqInv : A2 -> A1
  eqInv = isEqInv (snd e)

  eqSec : isSectionOf eqFun eqInv
  eqSec = isEqSec (snd e)

  eqRet : isRetractionOf eqFun eqInv
  eqRet = isEqRet (snd e)
