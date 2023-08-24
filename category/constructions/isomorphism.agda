{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import equality
open import sigma
open import sigma.base
open import hlevel.base
open import hlevel.sigma

module category.constructions.isomorphism where

module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  open CategoryHelpers C

  private
    IsoSorts : CategorySorts ℓO ℓM
    IsoSorts .CategorySorts.Obj = Obj C
    IsoSorts .CategorySorts.Mor a b = Σ (C [ a , b ]) (isIso C)

    IsoOps : CategoryOps IsoSorts
    IsoOps .CategoryOps.id = id C , is-iso (id C) ⋆-id² ⋆-id²
    IsoOps .CategoryOps._⋆_
      (f₁ , is-iso i₁ sec₁ ret₁) (f₂ , is-iso i₂ sec₂ ret₂) =
      (f₁ ⋆ f₂ , is-iso (i₂ ⋆ i₁) sec ret)
      where
      sec = ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> ⋆-left sec₁ >=> ⋆-left-id) >=> sec₂
      ret = ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> ⋆-left ret₂ >=> ⋆-left-id) >=> ret₁

    IsoLaws : CategoryLaws IsoOps
    IsoLaws .CategoryLaws.⋆-left-id f =
      ΣProp-path isProp-isIso ⋆-left-id
    IsoLaws .CategoryLaws.⋆-right-id f =
      ΣProp-path isProp-isIso ⋆-right-id
    IsoLaws .CategoryLaws.⋆-assoc f g h =
      ΣProp-path isProp-isIso ⋆-assoc
    IsoLaws .CategoryLaws.isSet-Mor =
      isSetΣ (isSet-Mor C) (\_ -> isProp->isSet isProp-isIso)

  IsoC : PreCategory ℓO ℓM
  IsoC = Laws->Category IsoLaws
