{-# OPTIONS --cubical --safe --exact-split #-}

module without-point where

open import base
open import equality
open import sigma

WithoutPoint : {ℓ : Level} (A : Type ℓ) -> (a : A) -> Type ℓ
WithoutPoint A a = Σ[ a2 ∈ A ] (a2 != a)
