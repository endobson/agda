{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.isomorphism where

open import category.monoidal.formal.base
open import category.constructions.triple-product
open import category.constructions.product
open import category.monoidal.base
open import category.base
open import category.isomorphism
open import base
open import equality-path


module InMonoidalIso
  {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C) (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open InMonoidal MC obj

  isIso-basic-mor : {a b : WObj} -> (m : BasicMor a b) -> isIso C (basic-mor->mor m)
  isIso-basic-mor (α⇒' a b c) = (snd associator) (triple (inj₀ a) (inj₀ b) (inj₀ c))
  isIso-basic-mor (λ⇒' o) = (snd unitorˡ) (inj₀ o)
  isIso-basic-mor (ρ⇒' o) = (snd unitorʳ) (inj₀ o)
  isIso-basic-mor (α⇐' a b c) = sym-isIso ((snd associator) (triple (inj₀ a) (inj₀ b) (inj₀ c)))
  isIso-basic-mor (λ⇐' o) = sym-isIso ((snd unitorˡ) (inj₀ o))
  isIso-basic-mor (ρ⇐' o) = sym-isIso ((snd unitorʳ) (inj₀ o))
  isIso-basic-mor (m ⊗ˡ' o) =
    functor-preserves-isIso (appʳ ⊗F (inj₀ o)) (isIso-basic-mor m)
  isIso-basic-mor (o ⊗ʳ' m) =
    functor-preserves-isIso (appˡ ⊗F (inj₀ o)) (isIso-basic-mor m)

  isIso-basic-path : {a b : WObj} -> (p : BasicPath a b) -> isIso C (basic-path->mor p)
  isIso-basic-path {a} (empty p) =
    transport (\i -> isIso C (transport-filler (\j -> C [ inj₀ a , inj₀ (p j) ]) (id C) i))
              (isIso-id C)
  isIso-basic-path {a} (m :: p) = isIso-⋆ (isIso-basic-mor m) (isIso-basic-path p)
