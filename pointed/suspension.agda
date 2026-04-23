{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.suspension where

open import base
open import pointed.base

data Susp {ℓ : Level} (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  meridian : (a : A) -> north == south


Susp∙' : {ℓ : Level} (A : Type ℓ) -> Type∙ ℓ
Susp∙' A = Susp A , north

Susp∙ : {ℓ : Level} (A : Type∙ ℓ) -> Type∙ ℓ
Susp∙ (A , _) = Susp∙' A

module _ {ℓA ℓP : Level} {A : Type ℓA} {P₁ P₂ : Type ℓP} (paths : A -> P₁ == P₂)
  where
  Susp-rec : Susp A -> Type ℓP
  Susp-rec north = P₁
  Susp-rec south = P₂
  Susp-rec (meridian a i) = paths a i
