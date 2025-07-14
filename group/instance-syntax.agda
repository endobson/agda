{-# OPTIONS --cubical --safe --exact-split #-}

module group.instance-syntax where

open import base
open import group

module _ {ℓ : Level} {D : Type ℓ} {{G : GroupStr D}} where
  open GroupStr G public hiding (isSet-Domain) renaming (inverse to _⁻¹)
