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
