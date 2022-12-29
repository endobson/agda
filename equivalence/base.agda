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

-- fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
-- fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

-- record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
--  no-eta-equality
--  field
--    equiv-proof : (y : B) → isContr (fiber f y)
