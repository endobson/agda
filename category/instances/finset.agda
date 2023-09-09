{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.finset where

open import base
open import category.base
open import category.displayed
open import category.instances.set
open import hlevel.base
open import relation
open import finset


module _ {ℓO ℓM ℓP : Level} (C : PreCategory ℓO ℓM) (P : Pred (Obj C) ℓP) where
  FullCᴰ : PreCategoryᴰ C ℓP ℓ-zero
  FullCᴰ .PreCategoryᴰ.Objᴰ = P
  FullCᴰ .PreCategoryᴰ.Morᴰ _ _ _ = Top
  FullCᴰ .PreCategoryᴰ.idᴰ = tt
  FullCᴰ .PreCategoryᴰ._⋆ᴰ_ _ _ = tt
  FullCᴰ .PreCategoryᴰ.⋆ᴰ-left-id _ = refl
  FullCᴰ .PreCategoryᴰ.⋆ᴰ-right-id _ = refl
  FullCᴰ .PreCategoryᴰ.⋆ᴰ-assoc _ _ _ = refl
  FullCᴰ .PreCategoryᴰ.isSet-Morᴰ = isProp->isSet isPropTop


FinSetCᴰ : (ℓ : Level) -> PreCategoryᴰ (SetC ℓ) ℓ ℓ-zero
FinSetCᴰ ℓ = FullCᴰ (SetC ℓ) (\ (S , _) -> isFinSetΣ S)

FinSetC : (ℓ : Level) -> PreCategory (ℓ-suc ℓ) ℓ
FinSetC ℓ = TotalC (FinSetCᴰ ℓ)
